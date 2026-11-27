import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0711
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0700
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0634
import ProximityPrize.SubmissionLower.Z6969Pack0641
import ProximityPrize.SubmissionLower.Z6969Pack0640
import ProximityPrize.SubmissionLower.Z6969Pack0642
import ProximityPrize.SubmissionLower.Z6969Pack0652
import ProximityPrize.SubmissionLower.Z6969Pack0643
import ProximityPrize.SubmissionLower.Z6969Pack0650
import ProximityPrize.SubmissionLower.Z6969Pack0644
import ProximityPrize.SubmissionLower.Z6969Pack0655
import ProximityPrize.SubmissionLower.Z6969Pack0646
import ProximityPrize.SubmissionLower.Z6969Pack0649
import ProximityPrize.SubmissionLower.Z6969Pack0645
import ProximityPrize.SubmissionLower.Z6969Pack0656
import ProximityPrize.SubmissionLower.Z6969Pack0657
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice
import ProximityPrize.SubmissionLower.Z6969FastCeil

set_option Elab.async false

-- merged module Z6969Pack0712
section Merged_Z6969Pack0712

-- Source: Research6969.PrefixMainDataQuarticIntervals1
section Z6969Source1608
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.QuarticIntervals1
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 20, 23, 25, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank35 2061, bank44 2409, bank53 2871, bank42 4552, bank61 2536, bank69 4787, bank72 2841, bank95 3103, bank115 3521, bank92 5432, bank140 3997, bank130 22726, bank164 6138, bank212 10770, bank186 46700, bank174 148759, bank169 292467] i
  head := src1550
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15471, 160609, 738157, 3373585],
    ![25417/2, 232127/2, 527033, 2411809],
    ![54680/9, 505990/9, 527033, 2304159],
    ![29433/8, 68147/2, 2468864/9, 3315752/3],
    ![5710/3, 103495/6, 703551/4, 2788533/4],
    ![18775/16, 353595/32, 3196512/25, 13037508/25],
    ![86808/121, 75858/11, 3753420/49, 8242641/25],
    ![73478/121, 75858/11, 3753420/49, 8242641/25],
    ![73478/121, 815372/121, 3662572/49, 13724832/49],
    ![73478/121, 815372/121, 3446640/49, 13724832/49],
    ![73478/121, 815372/121, 3446640/49, 13724832/49],
    ![73478/121, 815372/121, 3446640/49, 9628609/36],
    ![73478/121, 2441900/441, 897855/16, 1361118/7],
    ![73478/121, 2441900/441, 897855/16, 1361118/7],
    ![73478/121, 2441900/441, 897855/16, 1361118/7],
    ![33463/82, 2441900/441, 897855/16, 1361118/7],
    ![33463/82, 8092128/1681, 2272446/49, 8304714/49],
    ![33463/82, 5922252/1369, 6865875/169, 12888100/81],
    ![481425/1369, 5922252/1369, 6865875/169, 12888100/81],
    ![462882/1369, 5922252/1369, 6865875/169, 12888100/81],
    ![459151/1369, 5922252/1369, 6865875/169, 12888100/81]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 30 514727 := by
  refine ⟨?_, rank154 5412, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1550⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free35_0
    · exact free44_0
    · exact free53_0
    · exact free42_2
    · exact free61_0
    · exact free69_0
    · exact free72_0
    · exact free95_0
    · exact free115_0
    · exact free92_0
    · exact free140_0
    · exact free130_0
    · exact free164_0
    · exact free212_0
    · exact free186_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [305902360, 304802763, 305561139, 305664996, 304414993, 304778544, 305661345, 304833414, 163955059, 163955138, 163955797, 163822679, 58931745, 81498679, 74330152, 74251148, 91595014, 91608080, 118888003, 165463173, 228802845], [1160129, 1165754, 1161874, 1161343, 1167738, 1165878, 1161362, 1165597, 2334857, 2334856, 2334845, 2337058, 6841942, 4892988, 5381961, 5388240, 4334899, 4334240, 3294590, 2309783, 1622477],
  ![121453126182900, 1612631784120, 205922560500, 5158529810], 164646073898128238⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 18 _
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
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5922252/1369, 6865875/169, 12888100/81] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.QuarticIntervals1
end Z6969Source1608

-- Source: Research6969.PhysicalChecks093
section Z6969Source1609
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1288 : Request := ⟨⟨⟨560,781,172,7715⟩,5388141854720,10440670587⟩,3,4,1,514727,30⟩
private theorem pass1288_2293 : (Triangular src1288) 2293 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1288_2304 : (Triangular src1288) 2304 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1288_2339 : (Triangular src1288) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1288 : Cover (Triangular src1288) 2389 2293 [2303,2338,2389] := by
  exact ⟨by decide, by decide, pass1288_2293, by decide, by decide, pass1288_2304, by decide, by decide, pass1288_2339, rfl⟩
def src1289 : Request := ⟨⟨⟨690,962,208,9763⟩,9921631092736,23645774460⟩,6,4,1,514727,30⟩
private theorem pass1289_2293 : (Triangular src1289) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1289_2298 : (Triangular src1289) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1289_2313 : (Triangular src1289) 2313 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1289_2360 : (Triangular src1289) 2360 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1289 : Cover (Triangular src1289) 2389 2293 [2297,2312,2359,2389] := by
  exact ⟨by decide, by decide, pass1289_2293, by decide, by decide, pass1289_2298, by decide, by decide, pass1289_2313, by decide, by decide, pass1289_2360, rfl⟩
def src1290 : Request := ⟨⟨⟨825,1151,260,9763⟩,17518948515840,50057971890⟩,8,4,1,514727,30⟩
private theorem pass1290_2293 : (Triangular src1290) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1290_2296 : (Triangular src1290) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1290_2305 : (Triangular src1290) 2305 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1290_2332 : (Triangular src1290) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1290 : Cover (Triangular src1290) 2389 2293 [2295,2304,2331,2389] := by
  exact ⟨by decide, by decide, pass1290_2293, by decide, by decide, pass1290_2296, by decide, by decide, pass1290_2305, by decide, by decide, pass1290_2332, rfl⟩
def src1291 : Request := ⟨⟨⟨1200,1674,378,13899⟩,53798525730816,223406703910⟩,16,4,1,514727,30⟩
private theorem pass1291_2293 : (Triangular src1291) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1291_2297 : (Triangular src1291) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1291_2309 : (Triangular src1291) 2309 2343 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1291_2344 : (Triangular src1291) 2344 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1291 : Cover (Triangular src1291) 2389 2293 [2296,2308,2343,2389] := by
  exact ⟨by decide, by decide, pass1291_2293, by decide, by decide, pass1291_2297, by decide, by decide, pass1291_2309, by decide, by decide, pass1291_2344, rfl⟩
def src1292 : Request := ⟨⟨⟨2100,2929,645,28173⟩,282396798484480,2049139102608⟩,40,4,1,514727,30⟩
private theorem pass1292_2293 : (Triangular src1292) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1292_2298 : (Triangular src1292) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1292_2312 : (Triangular src1292) 2312 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1292_2352 : (Triangular src1292) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1292 : Cover (Triangular src1292) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass1292_2293, by decide, by decide, pass1292_2298, by decide, by decide, pass1292_2312, by decide, by decide, pass1292_2352, rfl⟩
def src1293 : Request := ⟨⟨⟨3950,5509,1213,164837⟩,1877062482395136,25607310424524⟩,110,4,1,514727,30⟩
private theorem pass1293_2293 : (Triangular src1293) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1293_2294 : (Triangular src1293) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1293_2296 : (Triangular src1293) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1293_2302 : (Triangular src1293) 2302 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1293_2318 : (Triangular src1293) 2318 2362 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1293_2363 : (Triangular src1293) 2363 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1293 : Cover (Triangular src1293) 2389 2293 [2293,2295,2301,2317,2362,2389] := by
  exact ⟨by decide, by decide, pass1293_2293, by decide, by decide, pass1293_2294, by decide, by decide, pass1293_2296, by decide, by decide, pass1293_2302, by decide, by decide, pass1293_2318, by decide, by decide, pass1293_2363, rfl⟩
def src1294 : Request := ⟨⟨⟨4800,6695,1474,72277⟩,3367547627110400,55837558620681⟩,110,4,1,514727,30⟩
private theorem pass1294_2293 : (Triangular src1294) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1294_2303 : (Triangular src1294) 2303 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1294_2331 : (Triangular src1294) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1294 : Cover (Triangular src1294) 2389 2293 [2302,2330,2389] := by
  exact ⟨by decide, by decide, pass1294_2293, by decide, by decide, pass1294_2303, by decide, by decide, pass1294_2331, rfl⟩
def src1295 : Request := ⟨⟨⟨8300,11577,2548,115771⟩,17399709518790656,498847383098023⟩,190,4,1,514727,30⟩
private theorem pass1295_2293 : (Triangular src1295) 2293 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1295_2304 : (Triangular src1295) 2304 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1295_2334 : (Triangular src1295) 2334 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1295 : Cover (Triangular src1295) 2389 2293 [2303,2333,2389] := by
  exact ⟨by decide, by decide, pass1295_2293, by decide, by decide, pass1295_2304, by decide, by decide, pass1295_2334, rfl⟩
def src1296 : Request := ⟨⟨⟨8300,11575,2548,422931⟩,17399709518790656,498569901356632⟩,245,4,1,514727,30⟩
private theorem pass1296_2293 : (Triangular src1296) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1296_2294 : (Triangular src1296) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1296_2297 : (Triangular src1296) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1296_2305 : (Triangular src1296) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1296_2327 : (Triangular src1296) 2327 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1296_2387 : (Triangular src1296) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1296 : Cover (Triangular src1296) 2389 2293 [2293,2296,2304,2326,2386,2389] := by
  exact ⟨by decide, by decide, pass1296_2293, by decide, by decide, pass1296_2294, by decide, by decide, pass1296_2297, by decide, by decide, pass1296_2305, by decide, by decide, pass1296_2327, by decide, by decide, pass1296_2387, rfl⟩
def src1299 : Request := ⟨⟨⟨400,558,123,4817⟩,1971918995456,2734096379⟩,0,4,1,514727,34⟩
private theorem pass1299_2293 : (Triangular src1299) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1299_2302 : (Triangular src1299) 2302 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1299_2332 : (Triangular src1299) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1299 : Cover (Triangular src1299) 2389 2293 [2301,2331,2389] := by
  exact ⟨by decide, by decide, pass1299_2293, by decide, by decide, pass1299_2302, by decide, by decide, pass1299_2332, rfl⟩
def src1300 : Request := ⟨⟨⟨470,655,141,5419⟩,3134317133824,5085275599⟩,1,4,1,514727,34⟩
private theorem pass1300_2293 : (Triangular src1300) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1300_2300 : (Triangular src1300) 2300 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1300_2323 : (Triangular src1300) 2323 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1300 : Cover (Triangular src1300) 2389 2293 [2299,2322,2389] := by
  exact ⟨by decide, by decide, pass1300_2293, by decide, by decide, pass1300_2300, by decide, by decide, pass1300_2323, rfl⟩
def src1301 : Request := ⟨⟨⟨470,655,144,6096⟩,3184589537280,5168862572⟩,2,4,1,514727,34⟩
private theorem pass1301_2293 : (Triangular src1301) 2293 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1301_2314 : (Triangular src1301) 2314 2382 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1301_2383 : (Triangular src1301) 2383 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1301 : Cover (Triangular src1301) 2389 2293 [2313,2382,2389] := by
  exact ⟨by decide, by decide, pass1301_2293, by decide, by decide, pass1301_2314, by decide, by decide, pass1301_2383, rfl⟩
def src1302 : Request := ⟨⟨⟨470,655,144,6858⟩,3184589537280,5168862572⟩,3,4,1,514727,34⟩
private theorem pass1302_2293 : (Triangular src1302) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1302_2296 : (Triangular src1302) 2296 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1302_2306 : (Triangular src1302) 2306 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1302_2338 : (Triangular src1302) 2338 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1302 : Cover (Triangular src1302) 2389 2293 [2295,2305,2337,2389] := by
  exact ⟨by decide, by decide, pass1302_2293, by decide, by decide, pass1302_2296, by decide, by decide, pass1302_2306, by decide, by decide, pass1302_2338, rfl⟩
def src1303 : Request := ⟨⟨⟨560,781,169,6858⟩,5316921262080,10299257375⟩,4,4,1,514727,34⟩
private theorem pass1303_2293 : (Triangular src1303) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1303_2295 : (Triangular src1303) 2295 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1303_2302 : (Triangular src1303) 2302 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1303_2324 : (Triangular src1303) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1303 : Cover (Triangular src1303) 2389 2293 [2294,2301,2323,2389] := by
  exact ⟨by decide, by decide, pass1303_2293, by decide, by decide, pass1303_2295, by decide, by decide, pass1303_2302, by decide, by decide, pass1303_2324, rfl⟩
def src1304 : Request := ⟨⟨⟨690,962,212,8679⟩,10065769922560,23997864317⟩,8,4,1,514727,34⟩
private theorem pass1304_2293 : (Triangular src1304) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1304_2302 : (Triangular src1304) 2302 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1304_2330 : (Triangular src1304) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1304 : Cover (Triangular src1304) 2389 2293 [2301,2329,2389] := by
  exact ⟨by decide, by decide, pass1304_2293, by decide, by decide, pass1304_2302, by decide, by decide, pass1304_2330, rfl⟩
def src1305 : Request := ⟨⟨⟨1200,1673,368,19788⟩,52718727069696,218387554859⟩,25,4,1,514727,34⟩
private theorem pass1305_2293 : (Triangular src1305) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1305_2297 : (Triangular src1305) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1305_2308 : (Triangular src1305) 2308 2339 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1305_2340 : (Triangular src1305) 2340 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1305 : Cover (Triangular src1305) 2389 2293 [2296,2307,2339,2389] := by
  exact ⟨by decide, by decide, pass1305_2293, by decide, by decide, pass1305_2297, by decide, by decide, pass1305_2308, by decide, by decide, pass1305_2340, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1609

-- Source: Research6969.PrefixRescueDataQuarticIntervals1
section Z6969Source1610
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals1
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,33⟩
  bank i := ![bank134 6858, bank142 6858, bank156 7715, bank192 9763, bank205 9763, bank229 13899, bank249 28173, bank324 72277, bank308 164837, bank365 115771, bank362 422931] i
  reserve i := ![0, 1, 3, 6, 8, 16, 40, 110, 110, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514727
  seedFloor := 30

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank134 6858
    · exact rank142 6858
    · exact rank156 7715
    · exact rank192 9763
    · exact rank205 9763
    · exact rank229 13899
    · exact rank249 28173
    · exact rank324 72277
    · exact rank308 164837
    · exact rank365 115771
    · exact rank362 422931
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1286⟩
    · exact ⟨_, cover1287⟩
    · exact ⟨_, cover1288⟩
    · exact ⟨_, cover1289⟩
    · exact ⟨_, cover1290⟩
    · exact ⟨_, cover1291⟩
    · exact ⟨_, cover1292⟩
    · exact ⟨_, cover1294⟩
    · exact ⟨_, cover1293⟩
    · exact ⟨_, cover1295⟩
    · exact ⟨_, cover1296⟩

def price : EarlyPrice := ⟨4, 33, 10, 70/100, 70/100, ![5433252875115, 609901615890, 32733302420, 2975770980], 1982886337759406⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![19219/246, 199855/191, 845125/191, 3820443/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.QuarticIntervals1
end Z6969Source1610

-- Source: Research6969.PrefixNearSavedQuarticIntervals1
section Z6969Source1611
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedQuarticIntervals1
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4325,78,1046,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.QuarticIntervals1.plan Lower6960.Prefix6969RescueData.QuarticIntervals1.plan Lower6960.Prefix6969RescueData.QuarticIntervals1.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 4 30 33 514727 :=
  ⟨Lower6960.Prefix6969MainCases.QuarticIntervals1.plan, Lower6960.Prefix6969MainCases.QuarticIntervals1.price, Lower6960.Prefix6969MainCases.QuarticIntervals1.valid, Lower6960.Prefix6969MainCases.QuarticIntervals1.priced, Lower6960.Prefix6969MainCases.QuarticIntervals1.sources,
   Lower6960.Prefix6969RescueData.QuarticIntervals1.plan, Lower6960.Prefix6969RescueData.QuarticIntervals1.price, Lower6960.Prefix6969RescueData.QuarticIntervals1.sources, Lower6960.Prefix6969RescueData.QuarticIntervals1.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 209827249971515584 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedQuarticIntervals1
end Z6969Source1611

-- Source: Research6969.PrefixMainDataQuarticIntervals2
section Z6969Source1612
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.QuarticIntervals2
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 21
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 18, 14, 18, 21, 21, 30, 41, 41, 76, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank37 2039, bank44 2409, bank54 2755, bank65 3612, bank69 4787, bank82 2965, bank104 3359, bank137 3540, bank114 3710, bank168 4492, bank131 21237, bank161 6246, bank214 10456, bank190 37026, bank179 76613, bank174 148759, bank169 292467] i
  head := src1551
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  historyValues := [![15845, 158523, 730701, 3268911],
    ![25417/2, 455559/4, 521808, 2411809],
    ![54680/9, 165530/3, 521808, 8816431/4],
    ![29433/8, 535071/16, 807758/3, 9515326/9],
    ![64334/25, 570569/25, 204050, 3705625/4],
    ![17323/9, 610657/36, 2749287/16, 10555903/16],
    ![18775/16, 694265/64, 3138467/25, 12471393/25],
    ![89110/121, 804855/121, 3648898/49, 303601],
    ![89110/121, 804855/121, 3648898/49, 303601],
    ![221128/361, 804855/121, 3446640/49, 303601],
    ![221128/361, 804855/121, 3446640/49, 303601],
    ![221128/361, 2218876/361, 3090280/49, 11282881/49],
    ![221128/361, 646388/121, 2841885/49, 9163290/49],
    ![221128/361, 58024/11, 5499213/98, 9163290/49],
    ![221128/361, 58024/11, 5499213/98, 20178064/121],
    ![688141/1681, 58024/11, 5499213/98, 20178064/121],
    ![688141/1681, 7912596/1681, 8896211/196, 20178064/121],
    ![688141/1681, 5792346/1369, 104230987/2601, 109327936/729],
    ![489643/1369, 5792346/1369, 104230987/2601, 109327936/729],
    ![470505/1369, 5792346/1369, 104230987/2601, 109327936/729],
    ![462882/1369, 5792346/1369, 104230987/2601, 109327936/729],
    ![459151/1369, 5792346/1369, 104230987/2601, 109327936/729]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 34 514727 := by
  refine ⟨?_, rank154 5177, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1551⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free65_0
    · exact free69_0
    · exact free82_0
    · exact free104_0
    · exact free137_0
    · exact free114_0
    · exact free168_0
    · exact free131_0
    · exact free161_0
    · exact free214_0
    · exact free190_0
    · exact free179_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [301679581, 301333188, 299406335, 300849015, 300034565, 300181871, 300437441, 129714449, 129037580, 129280863, 127934186, 127417410, 68525359, 100245077, 63868360, 59336897, 88683276, 88686852, 92918911, 116643406, 164405171, 227993477], [1181732, 1183504, 1193361, 1185981, 1190147, 1189394, 1188086, 2995449, 3010868, 3004955, 3041713, 3056159, 5858176, 3944309, 6300297, 6795307, 4481729, 4481549, 4268139, 3357336, 2327373, 1629131],
  ![121023497461140, 1613505895888, 205194129300, 5333257510], 161348404820216006⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
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
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5792346/1369, 104230987/2601, 109327936/729] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.QuarticIntervals2
end Z6969Source1612

-- Source: Research6969.PhysicalChecks094
section Z6969Source1613
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1306 : Request := ⟨⟨⟨2600,3626,798,40111⟩,535425056505856,4807957255301⟩,65,4,1,514727,34⟩
private theorem pass1306_2293 : (Triangular src1306) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1306_2298 : (Triangular src1306) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1306_2312 : (Triangular src1306) 2312 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1306_2351 : (Triangular src1306) 2351 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1306 : Cover (Triangular src1306) 2389 2293 [2297,2311,2350,2389] := by
  exact ⟨by decide, by decide, pass1306_2293, by decide, by decide, pass1306_2298, by decide, by decide, pass1306_2312, by decide, by decide, pass1306_2351, rfl⟩
def src1307 : Request := ⟨⟨⟨6900,9623,2174,102908⟩,10196763128627200,243058712908678⟩,190,4,1,514727,34⟩
private theorem pass1307_2293 : (Triangular src1307) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1307_2296 : (Triangular src1307) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1307_2304 : (Triangular src1307) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1307_2326 : (Triangular src1307) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1307_2387 : (Triangular src1307) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1307 : Cover (Triangular src1307) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass1307_2293, by decide, by decide, pass1307_2296, by decide, by decide, pass1307_2304, by decide, by decide, pass1307_2326, by decide, by decide, pass1307_2387, rfl⟩
def src1308 : Request := ⟨⟨⟨8300,11575,2615,164837⟩,17745461310914560,508734991702659⟩,245,4,1,514727,34⟩
private theorem pass1308_2293 : (Triangular src1308) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1308_2294 : (Triangular src1308) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1308_2296 : (Triangular src1308) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1308_2302 : (Triangular src1308) 2302 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1308_2318 : (Triangular src1308) 2318 2361 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1308_2362 : (Triangular src1308) 2362 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1308 : Cover (Triangular src1308) 2389 2293 [2293,2295,2301,2317,2361,2389] := by
  exact ⟨by decide, by decide, pass1308_2293, by decide, by decide, pass1308_2294, by decide, by decide, pass1308_2296, by decide, by decide, pass1308_2302, by decide, by decide, pass1308_2318, by decide, by decide, pass1308_2362, rfl⟩
def src1309 : Request := ⟨⟨⟨10000,13948,3070,115771⟩,30428373265940480,1050983571587703⟩,245,4,1,514727,34⟩
private theorem pass1309_2293 : (Triangular src1309) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1309_2301 : (Triangular src1309) 2301 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1309_2323 : (Triangular src1309) 2323 2383 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1309_2384 : (Triangular src1309) 2384 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1309 : Cover (Triangular src1309) 2389 2293 [2300,2322,2383,2389] := by
  exact ⟨by decide, by decide, pass1309_2293, by decide, by decide, pass1309_2301, by decide, by decide, pass1309_2323, by decide, by decide, pass1309_2384, rfl⟩
def src1310 : Request := ⟨⟨⟨325,453,100,4817⟩,1061047500800,1193036697⟩,0,4,1,514727,38⟩
private theorem pass1310_2293 : (Triangular src1310) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1310_2296 : (Triangular src1310) 2296 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1310_2306 : (Triangular src1310) 2306 2341 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1310_2342 : (Triangular src1310) 2342 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1310 : Cover (Triangular src1310) 2389 2293 [2295,2305,2341,2389] := by
  exact ⟨by decide, by decide, pass1310_2293, by decide, by decide, pass1310_2296, by decide, by decide, pass1310_2306, by decide, by decide, pass1310_2342, rfl⟩
def src1311 : Request := ⟨⟨⟨400,558,120,4817⟩,1935519252480,2682384904⟩,1,4,1,514727,38⟩
private theorem pass1311_2293 : (Triangular src1311) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1311_2297 : (Triangular src1311) 2297 2310 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1311_2311 : (Triangular src1311) 2311 2357 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1311_2358 : (Triangular src1311) 2358 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1311 : Cover (Triangular src1311) 2389 2293 [2296,2310,2357,2389] := by
  exact ⟨by decide, by decide, pass1311_2293, by decide, by decide, pass1311_2297, by decide, by decide, pass1311_2311, by decide, by decide, pass1311_2358, rfl⟩
def src1312 : Request := ⟨⟨⟨400,558,123,5419⟩,1971918995456,2734096379⟩,2,4,1,514727,38⟩
private theorem pass1312_2293 : (Triangular src1312) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1312_2300 : (Triangular src1312) 2300 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1312_2324 : (Triangular src1312) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1312 : Cover (Triangular src1312) 2389 2293 [2299,2323,2389] := by
  exact ⟨by decide, by decide, pass1312_2293, by decide, by decide, pass1312_2300, by decide, by decide, pass1312_2324, rfl⟩
def src1313 : Request := ⟨⟨⟨470,655,144,6096⟩,3184589537280,5168862572⟩,4,4,1,514727,38⟩
private theorem pass1313_2293 : (Triangular src1313) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1313_2299 : (Triangular src1313) 2299 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1313_2319 : (Triangular src1313) 2319 2384 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1313_2385 : (Triangular src1313) 2385 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1313 : Cover (Triangular src1313) 2389 2293 [2298,2318,2384,2389] := by
  exact ⟨by decide, by decide, pass1313_2293, by decide, by decide, pass1313_2299, by decide, by decide, pass1313_2319, by decide, by decide, pass1313_2385, rfl⟩
def src1314 : Request := ⟨⟨⟨560,781,169,6858⟩,5316921262080,10299257375⟩,6,4,1,514727,38⟩
private theorem pass1314_2293 : (Triangular src1314) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1314_2295 : (Triangular src1314) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1314_2301 : (Triangular src1314) 2301 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1314_2320 : (Triangular src1314) 2320 2380 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1314_2381 : (Triangular src1314) 2381 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1314 : Cover (Triangular src1314) 2389 2293 [2294,2300,2319,2380,2389] := by
  exact ⟨by decide, by decide, pass1314_2293, by decide, by decide, pass1314_2295, by decide, by decide, pass1314_2301, by decide, by decide, pass1314_2320, by decide, by decide, pass1314_2381, rfl⟩
def src1315 : Request := ⟨⟨⟨690,962,208,8679⟩,9921631092736,23645774460⟩,10,4,1,514727,38⟩
private theorem pass1315_2293 : (Triangular src1315) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1315_2295 : (Triangular src1315) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1315_2301 : (Triangular src1315) 2301 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1315_2320 : (Triangular src1315) 2320 2378 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1315_2379 : (Triangular src1315) 2379 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1315 : Cover (Triangular src1315) 2389 2293 [2294,2300,2319,2378,2389] := by
  exact ⟨by decide, by decide, pass1315_2293, by decide, by decide, pass1315_2295, by decide, by decide, pass1315_2301, by decide, by decide, pass1315_2320, by decide, by decide, pass1315_2379, rfl⟩
def src1316 : Request := ⟨⟨⟨1000,1395,307,12355⟩,30557599170560,105715278267⟩,20,4,1,514727,38⟩
private theorem pass1316_2293 : (Triangular src1316) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1316_2294 : (Triangular src1316) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1316_2297 : (Triangular src1316) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1316_2306 : (Triangular src1316) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1316_2332 : (Triangular src1316) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1316 : Cover (Triangular src1316) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass1316_2293, by decide, by decide, pass1316_2294, by decide, by decide, pass1316_2297, by decide, by decide, pass1316_2306, by decide, by decide, pass1316_2332, rfl⟩
def src1317 : Request := ⟨⟨⟨1750,2441,537,19788⟩,163381988556800,988269431527⟩,40,4,1,514727,38⟩
private theorem pass1317_2293 : (Triangular src1317) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1317_2301 : (Triangular src1317) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1317_2324 : (Triangular src1317) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1317 : Cover (Triangular src1317) 2389 2293 [2300,2323,2389] := by
  exact ⟨by decide, by decide, pass1317_2293, by decide, by decide, pass1317_2301, by decide, by decide, pass1317_2324, rfl⟩
def src1318 : Request := ⟨⟨⟨2600,3626,819,28173⟩,546063062138880,4905972788959⟩,65,4,1,514727,38⟩
private theorem pass1318_2293 : (Triangular src1318) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1318_2295 : (Triangular src1318) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1318_2301 : (Triangular src1318) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1318_2318 : (Triangular src1318) 2318 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1318_2366 : (Triangular src1318) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1318 : Cover (Triangular src1318) 2389 2293 [2294,2300,2317,2365,2389] := by
  exact ⟨by decide, by decide, pass1318_2293, by decide, by decide, pass1318_2295, by decide, by decide, pass1318_2301, by decide, by decide, pass1318_2318, by decide, by decide, pass1318_2366, rfl⟩
def src1319 : Request := ⟨⟨⟨4800,6694,1512,72277⟩,3433136573644800,56926029739529⟩,145,4,1,514727,38⟩
private theorem pass1319_2293 : (Triangular src1319) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1319_2297 : (Triangular src1319) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1319_2308 : (Triangular src1319) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1319_2339 : (Triangular src1319) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1319 : Cover (Triangular src1319) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass1319_2293, by decide, by decide, pass1319_2297, by decide, by decide, pass1319_2308, by decide, by decide, pass1319_2339, rfl⟩
def src1320 : Request := ⟨⟨⟨8300,11575,2615,102908⟩,17745461310914560,508734991702659⟩,245,4,1,514727,38⟩
private theorem pass1320_2293 : (Triangular src1320) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1320_2297 : (Triangular src1320) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1320_2308 : (Triangular src1320) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1320_2339 : (Triangular src1320) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1320 : Cover (Triangular src1320) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass1320_2293, by decide, by decide, pass1320_2297, by decide, by decide, pass1320_2308, by decide, by decide, pass1320_2339, rfl⟩
def src1321 : Request := ⟨⟨⟨325,453,100,3807⟩,1061047500800,1193036697⟩,0,4,1,514727,41⟩
private theorem pass1321_2293 : (Triangular src1321) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1321_2301 : (Triangular src1321) 2301 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1321_2330 : (Triangular src1321) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1321 : Cover (Triangular src1321) 2389 2293 [2300,2329,2389] := by
  exact ⟨by decide, by decide, pass1321_2293, by decide, by decide, pass1321_2301, by decide, by decide, pass1321_2330, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1613

-- Source: Research6969.PrefixRescueDataQuarticIntervals2
section Z6969Source1614
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals2
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,37⟩
  bank i := ![bank134 4817, bank141 5419, bank142 6096, bank142 6858, bank155 6858, bank193 8679, bank224 19788, bank264 40111, bank375 115771, bank363 164837, bank352 102908] i
  reserve i := ![0, 1, 2, 3, 4, 8, 25, 65, 245, 245, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514727
  seedFloor := 34

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank134 4817
    · exact rank141 5419
    · exact rank142 6096
    · exact rank142 6858
    · exact rank155 6858
    · exact rank193 8679
    · exact rank224 19788
    · exact rank264 40111
    · exact rank375 115771
    · exact rank363 164837
    · exact rank352 102908
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1299⟩
    · exact ⟨_, cover1300⟩
    · exact ⟨_, cover1301⟩
    · exact ⟨_, cover1302⟩
    · exact ⟨_, cover1303⟩
    · exact ⟨_, cover1304⟩
    · exact ⟨_, cover1305⟩
    · exact ⟨_, cover1306⟩
    · exact ⟨_, cover1309⟩
    · exact ⟨_, cover1308⟩
    · exact ⟨_, cover1307⟩

def price : EarlyPrice := ⟨4, 37, 10, 70/100, 70/100, ![2374285114732, 321569030305, 44219776520, 3585406950], 1331105980923960⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![9710/123, 229361/246, 489580/123, 4283527/246] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.QuarticIntervals2
end Z6969Source1614

-- Source: Research6969.PrefixNearSavedQuarticIntervals2
section Z6969Source1615
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedQuarticIntervals2
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4231,78,932,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.QuarticIntervals2.plan Lower6960.Prefix6969RescueData.QuarticIntervals2.plan Lower6960.Prefix6969RescueData.QuarticIntervals2.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 4 34 37 514727 :=
  ⟨Lower6960.Prefix6969MainCases.QuarticIntervals2.plan, Lower6960.Prefix6969MainCases.QuarticIntervals2.price, Lower6960.Prefix6969MainCases.QuarticIntervals2.valid, Lower6960.Prefix6969MainCases.QuarticIntervals2.priced, Lower6960.Prefix6969MainCases.QuarticIntervals2.sources,
   Lower6960.Prefix6969RescueData.QuarticIntervals2.plan, Lower6960.Prefix6969RescueData.QuarticIntervals2.price, Lower6960.Prefix6969RescueData.QuarticIntervals2.sources, Lower6960.Prefix6969RescueData.QuarticIntervals2.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 209733565312895538 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedQuarticIntervals2
end Z6969Source1615

-- Source: Research6969.PrefixMainDataQuarticIntervals3
section Z6969Source1616
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.QuarticIntervals3
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 21, 23, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank35 2061, bank44 2409, bank53 2871, bank42 4552, bank61 2536, bank69 4787, bank72 2841, bank95 3103, bank113 3716, bank138 3813, bank144 4704, bank131 21237, bank164 6138, bank214 10456, bank186 46700, bank174 148759, bank169 292467] i
  head := src1552
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15734, 158609, 729394, 3291536],
    ![25417/2, 447567/4, 521808, 2411809],
    ![54680/9, 162650/3, 521808, 8448583/4],
    ![29433/8, 525783/16, 793790/3, 9118318/9],
    ![5710/3, 149605/9, 1356139/8, 10224621/16],
    ![18775/16, 682385/64, 617023/5, 11951049/25],
    ![86808/121, 73234/11, 3625336/49, 8242641/25],
    ![73478/121, 73234/11, 3625336/49, 8242641/25],
    ![73478/121, 783351/121, 3520507/49, 6431296/25],
    ![73478/121, 783351/121, 3446640/49, 6431296/25],
    ![73478/121, 783351/121, 3446640/49, 6431296/25],
    ![73478/121, 783351/121, 3446640/49, 254446],
    ![73478/121, 626507/121, 2689509/49, 9217538/49],
    ![73478/121, 626507/121, 2689509/49, 9217538/49],
    ![73478/121, 1538869/300, 6256320/121, 4375602/25],
    ![688141/1681, 1538869/300, 6256320/121, 4375602/25],
    ![688141/1681, 7765604/1681, 311685/7, 13533608/81],
    ![688141/1681, 5680458/1369, 6014099/153, 90776378/625],
    ![481425/1369, 5680458/1369, 6014099/153, 90776378/625],
    ![462882/1369, 5680458/1369, 6014099/153, 90776378/625],
    ![459151/1369, 5680458/1369, 6014099/153, 90776378/625]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 38 514727 := by
  refine ⟨?_, rank154 4961, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1552⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free35_0
    · exact free44_0
    · exact free53_0
    · exact free42_2
    · exact free61_0
    · exact free69_0
    · exact free72_0
    · exact free95_0
    · exact free113_0
    · exact free138_0
    · exact free144_0
    · exact free131_0
    · exact free164_0
    · exact free214_0
    · exact free186_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [297535972, 297359944, 295907052, 297159107, 296532082, 296008603, 295907211, 302139850, 161061189, 160916332, 161031887, 161065120, 82059243, 82042919, 68458490, 68476484, 91654113, 91595608, 116574538, 163149708, 227036044], [1202929, 1203830, 1211263, 1204857, 1208065, 1210743, 1211262, 1179377, 2382971, 2385380, 2383459, 2382906, 4859701, 4860671, 5864236, 5862606, 4331918, 4334869, 3359261, 2348247, 1637003],
  ![120515272876080, 1614540300956, 204332439600, 5158494110], 159441561287073656⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5680458/1369, 6014099/153, 90776378/625] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.QuarticIntervals3
end Z6969Source1616

-- Source: Research6969.PrefixRescueDataQuarticIntervals3
section Z6969Source1617
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals3
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,40⟩
  bank i := ![bank101 4817, bank133 4817, bank134 5419, bank142 6096, bank155 6858, bank192 8679, bank222 12355, bank242 19788, bank265 28173, bank323 72277, bank363 102908] i
  reserve i := ![0, 1, 2, 4, 6, 10, 20, 40, 65, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514727
  seedFloor := 38

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 4817
    · exact rank133 4817
    · exact rank134 5419
    · exact rank142 6096
    · exact rank155 6858
    · exact rank192 8679
    · exact rank222 12355
    · exact rank242 19788
    · exact rank265 28173
    · exact rank323 72277
    · exact rank363 102908
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1310⟩
    · exact ⟨_, cover1311⟩
    · exact ⟨_, cover1312⟩
    · exact ⟨_, cover1313⟩
    · exact ⟨_, cover1314⟩
    · exact ⟨_, cover1315⟩
    · exact ⟨_, cover1316⟩
    · exact ⟨_, cover1317⟩
    · exact ⟨_, cover1318⟩
    · exact ⟨_, cover1319⟩
    · exact ⟨_, cover1320⟩

def price : EarlyPrice := ⟨4, 40, 10, 65/100, 60/100, ![1602453944312, 259707267020, 40720032110, 3054019275], 1010659220301247⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5615/73, 103754/123, 145772/41, 2058160/123] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.QuarticIntervals3
end Z6969Source1617

-- Source: Research6969.PrefixNearSavedQuarticIntervals3
section Z6969Source1618
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedQuarticIntervals3
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4149,76,843,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.QuarticIntervals3.plan Lower6960.Prefix6969RescueData.QuarticIntervals3.plan Lower6960.Prefix6969RescueData.QuarticIntervals3.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 4 38 40 514727 :=
  ⟨Lower6960.Prefix6969MainCases.QuarticIntervals3.plan, Lower6960.Prefix6969MainCases.QuarticIntervals3.price, Lower6960.Prefix6969MainCases.QuarticIntervals3.valid, Lower6960.Prefix6969MainCases.QuarticIntervals3.priced, Lower6960.Prefix6969MainCases.QuarticIntervals3.sources,
   Lower6960.Prefix6969RescueData.QuarticIntervals3.plan, Lower6960.Prefix6969RescueData.QuarticIntervals3.price, Lower6960.Prefix6969RescueData.QuarticIntervals3.sources, Lower6960.Prefix6969RescueData.QuarticIntervals3.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 209201397277186367 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedQuarticIntervals3
end Z6969Source1618

-- Source: Research6969.PrefixMainDataQuarticIntervals4
section Z6969Source1619
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.QuarticIntervals4
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 9, 10, 15, 14, 20, 18, 21, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank39 1983, bank46 2247, bank55 2427, bank53 2871, bank65 3612, bank82 2965, bank87 4698, bank105 3304, bank137 3540, bank144 4704, bank131 21237, bank164 6138, bank214 10456, bank186 46700, bank175 125592, bank169 292467] i
  head := src1553
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15974, 156708, 720671, 3129300],
    ![25417/2, 442017/4, 521808, 2411809],
    ![54680/9, 53550, 521808, 8193133/4],
    ![29433/8, 519333/16, 784090/3, 8842618/9],
    ![64334/25, 553367/25, 204050, 3705625/4],
    ![11819/6, 293641/18, 2651839/16, 9540213/16],
    ![2483/2, 165257/16, 2995166/25, 10810317/25],
    ![45497/50, 734927/100, 361623/4, 3892099/12],
    ![86808/121, 795974/121, 3582736/49, 3892099/12],
    ![86808/121, 795974/121, 3582736/49, 3892099/12],
    ![86808/121, 795974/121, 3582736/49, 2852923/10],
    ![27452/49, 279442/49, 467451/8, 272484],
    ![27452/49, 279442/49, 467451/8, 1986943/9],
    ![27452/49, 622964/121, 2737575/49, 8515470/49],
    ![27452/49, 1516519/300, 20492409/400, 4243302/25],
    ![688141/1681, 1516519/300, 20492409/400, 4243302/25],
    ![688141/1681, 7657004/1681, 2151645/49, 13124408/81],
    ![688141/1681, 5602758/1369, 100856833/2601, 88031678/625],
    ![481425/1369, 5602758/1369, 100856833/2601, 88031678/625],
    ![929061/2738, 5602758/1369, 100856833/2601, 88031678/625],
    ![459151/1369, 5602758/1369, 100856833/2601, 88031678/625]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 41 514727 := by
  refine ⟨?_, rank154 4811, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1553⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free39_0
    · exact free46_0
    · exact free55_0
    · exact free53_0
    · exact free65_0
    · exact free82_0
    · exact free87_1
    · exact free105_0
    · exact free137_0
    · exact free144_0
    · exact free131_0
    · exact free164_0
    · exact free214_0
    · exact free186_0
    · exact free175_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [293703200, 293120772, 292630037, 292615054, 292793544, 293182102, 293718789, 220000000, 147343005, 147345410, 147219505, 146920865, 147117200, 94617548, 66588137, 75779345, 86987117, 87064495, 107555739, 162630037, 226371160], [1222537, 1225517, 1228027, 1228104, 1227191, 1225203, 1222457, 1694852, 2611054, 2611014, 2613107, 2618202, 2614808, 4182481, 6033732, 5277382, 4567261, 4563359, 3662869, 2356887, 1642470],
  ![120162339151200, 1615258814840, 203734044000, 5435040590], 156558256562144665⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5602758/1369, 100856833/2601, 88031678/625] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.QuarticIntervals4
end Z6969Source1619

end Merged_Z6969Pack0712

-- merged module Z6969Pack0713
section Merged_Z6969Pack0713

-- Source: Research6969.PhysicalChecks095
section Z6969Source1620
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1322 : Request := ⟨⟨⟨400,558,126,3807⟩,2007957766144,2785382344⟩,1,4,1,514727,41⟩
private theorem pass1322_2293 : (Triangular src1322) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1322_2298 : (Triangular src1322) 2298 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1322_2315 : (Triangular src1322) 2315 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1322_2372 : (Triangular src1322) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1322 : Cover (Triangular src1322) 2389 2293 [2297,2314,2371,2389] := by
  exact ⟨by decide, by decide, pass1322_2293, by decide, by decide, pass1322_2298, by decide, by decide, pass1322_2315, by decide, by decide, pass1322_2372, rfl⟩
def src1323 : Request := ⟨⟨⟨400,558,126,4282⟩,2007957766144,2785382344⟩,2,4,1,514727,41⟩
private theorem pass1323_2293 : (Triangular src1323) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1323_2295 : (Triangular src1323) 2295 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1323_2302 : (Triangular src1323) 2302 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1323_2325 : (Triangular src1323) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1323 : Cover (Triangular src1323) 2389 2293 [2294,2301,2324,2389] := by
  exact ⟨by decide, by decide, pass1323_2293, by decide, by decide, pass1323_2295, by decide, by decide, pass1323_2302, by decide, by decide, pass1323_2325, rfl⟩
def src1324 : Request := ⟨⟨⟨400,558,123,5419⟩,1971918995456,2734096379⟩,3,4,1,514727,41⟩
private theorem pass1324_2293 : (Triangular src1324) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1324_2299 : (Triangular src1324) 2299 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1324_2319 : (Triangular src1324) 2319 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1324_2387 : (Triangular src1324) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1324 : Cover (Triangular src1324) 2389 2293 [2298,2318,2386,2389] := by
  exact ⟨by decide, by decide, pass1324_2293, by decide, by decide, pass1324_2299, by decide, by decide, pass1324_2319, by decide, by decide, pass1324_2387, rfl⟩
def src1325 : Request := ⟨⟨⟨470,655,141,5419⟩,3134317133824,5085275599⟩,4,4,1,514727,41⟩
private theorem pass1325_2293 : (Triangular src1325) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1325_2295 : (Triangular src1325) 2295 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1325_2302 : (Triangular src1325) 2302 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1325_2325 : (Triangular src1325) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1325 : Cover (Triangular src1325) 2389 2293 [2294,2301,2324,2389] := by
  exact ⟨by decide, by decide, pass1325_2293, by decide, by decide, pass1325_2295, by decide, by decide, pass1325_2302, by decide, by decide, pass1325_2325, rfl⟩
def src1326 : Request := ⟨⟨⟨560,781,176,6858⟩,5482316038144,10627925923⟩,8,4,1,514727,41⟩
private theorem pass1326_2293 : (Triangular src1326) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1326_2299 : (Triangular src1326) 2299 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1326_2318 : (Triangular src1326) 2318 2377 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1326_2378 : (Triangular src1326) 2378 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1326 : Cover (Triangular src1326) 2389 2293 [2298,2317,2377,2389] := by
  exact ⟨by decide, by decide, pass1326_2293, by decide, by decide, pass1326_2299, by decide, by decide, pass1326_2318, by decide, by decide, pass1326_2378, rfl⟩
def src1327 : Request := ⟨⟨⟨825,1150,253,9763⟩,17161575202816,48873782027⟩,16,4,1,514727,41⟩
private theorem pass1327_2293 : (Triangular src1327) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1327_2302 : (Triangular src1327) 2302 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1327_2329 : (Triangular src1327) 2329 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1327 : Cover (Triangular src1327) 2389 2293 [2301,2328,2389] := by
  exact ⟨by decide, by decide, pass1327_2293, by decide, by decide, pass1327_2302, by decide, by decide, pass1327_2329, rfl⟩
def src1330 : Request := ⟨⟨⟨3200,4463,1008,31694⟩,1017717693874176,11254299374432⟩,85,4,1,514727,41⟩
private theorem pass1330_2293 : (Triangular src1330) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1330_2298 : (Triangular src1330) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1330_2312 : (Triangular src1330) 2312 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1330_2351 : (Triangular src1330) 2351 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1330 : Cover (Triangular src1330) 2389 2293 [2297,2311,2350,2389] := by
  exact ⟨by decide, by decide, pass1330_2293, by decide, by decide, pass1330_2298, by decide, by decide, pass1330_2312, by decide, by decide, pass1330_2351, rfl⟩
def src1331 : Request := ⟨⟨⟨4800,6694,1474,57109⟩,3367547627110400,55810706074581⟩,145,4,1,514727,41⟩
private theorem pass1331_2293 : (Triangular src1331) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1331_2298 : (Triangular src1331) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1331_2312 : (Triangular src1331) 2312 2349 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1331_2350 : (Triangular src1331) 2350 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1331 : Cover (Triangular src1331) 2389 2293 [2297,2311,2349,2389] := by
  exact ⟨by decide, by decide, pass1331_2293, by decide, by decide, pass1331_2298, by decide, by decide, pass1331_2312, by decide, by decide, pass1331_2350, rfl⟩
def src1332 : Request := ⟨⟨⟨5700,7948,1796,91474⟩,5749327563587584,113150499898987⟩,190,4,1,514727,41⟩
private theorem pass1332_2293 : (Triangular src1332) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1332_2295 : (Triangular src1332) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1332_2301 : (Triangular src1332) 2301 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1332_2317 : (Triangular src1332) 2317 2360 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1332_2361 : (Triangular src1332) 2361 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1332 : Cover (Triangular src1332) 2389 2293 [2294,2300,2316,2360,2389] := by
  exact ⟨by decide, by decide, pass1332_2293, by decide, by decide, pass1332_2295, by decide, by decide, pass1332_2301, by decide, by decide, pass1332_2317, by decide, by decide, pass1332_2361, rfl⟩
def src1333 : Request := ⟨⟨⟨8300,11575,2548,91474⟩,17399709518790656,498569901356632⟩,245,4,1,514727,41⟩
private theorem pass1333_2293 : (Triangular src1333) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1333_2306 : (Triangular src1333) 2306 2341 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1333_2342 : (Triangular src1333) 2342 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1333 : Cover (Triangular src1333) 2389 2293 [2305,2341,2389] := by
  exact ⟨by decide, by decide, pass1333_2293, by decide, by decide, pass1333_2306, by decide, by decide, pass1333_2342, rfl⟩
def src1334 : Request := ⟨⟨⟨325,453,98,3384⟩,1045036793856,1174588250⟩,0,4,1,514727,45⟩
private theorem pass1334_2293 : (Triangular src1334) 2293 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1334_2307 : (Triangular src1334) 2307 2357 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1334_2358 : (Triangular src1334) 2358 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1334 : Cover (Triangular src1334) 2389 2293 [2306,2357,2389] := by
  exact ⟨by decide, by decide, pass1334_2293, by decide, by decide, pass1334_2307, by decide, by decide, pass1334_2358, rfl⟩
def src1335 : Request := ⟨⟨⟨325,453,100,3807⟩,1061047500800,1193036697⟩,1,4,1,514727,45⟩
private theorem pass1335_2293 : (Triangular src1335) 2293 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1335_2304 : (Triangular src1335) 2304 2342 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1335_2343 : (Triangular src1335) 2343 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1335 : Cover (Triangular src1335) 2389 2293 [2303,2342,2389] := by
  exact ⟨by decide, by decide, pass1335_2293, by decide, by decide, pass1335_2304, by decide, by decide, pass1335_2343, rfl⟩
def src1336 : Request := ⟨⟨⟨400,558,123,3807⟩,1971918995456,2734096379⟩,2,4,1,514727,45⟩
private theorem pass1336_2293 : (Triangular src1336) 2293 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1336_2307 : (Triangular src1336) 2307 2353 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1336_2354 : (Triangular src1336) 2354 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1336 : Cover (Triangular src1336) 2389 2293 [2306,2353,2389] := by
  exact ⟨by decide, by decide, pass1336_2293, by decide, by decide, pass1336_2307, by decide, by decide, pass1336_2354, rfl⟩
def src1337 : Request := ⟨⟨⟨400,558,123,4282⟩,1971918995456,2734096379⟩,3,4,1,514727,45⟩
private theorem pass1337_2293 : (Triangular src1337) 2293 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1337_2305 : (Triangular src1337) 2305 2345 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1337_2346 : (Triangular src1337) 2346 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1337 : Cover (Triangular src1337) 2389 2293 [2304,2345,2389] := by
  exact ⟨by decide, by decide, pass1337_2293, by decide, by decide, pass1337_2305, by decide, by decide, pass1337_2346, rfl⟩
def src1338 : Request := ⟨⟨⟨400,558,123,5419⟩,1971918995456,2734096379⟩,4,4,1,514727,45⟩
private theorem pass1338_2293 : (Triangular src1338) 2293 2310 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1338_2311 : (Triangular src1338) 2311 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1338_2372 : (Triangular src1338) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1338 : Cover (Triangular src1338) 2389 2293 [2310,2371,2389] := by
  exact ⟨by decide, by decide, pass1338_2293, by decide, by decide, pass1338_2311, by decide, by decide, pass1338_2372, rfl⟩
def src1339 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,6,4,1,514727,45⟩
private theorem pass1339_2293 : (Triangular src1339) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1339_2301 : (Triangular src1339) 2301 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1339_2327 : (Triangular src1339) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1339 : Cover (Triangular src1339) 2389 2293 [2300,2326,2389] := by
  exact ⟨by decide, by decide, pass1339_2293, by decide, by decide, pass1339_2301, by decide, by decide, pass1339_2327, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1620

-- Source: Research6969.PrefixRescueDataQuarticIntervals4
section Z6969Source1621
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals4
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,44⟩
  bank i := ![bank101 3807, bank135 3807, bank135 4282, bank134 5419, bank141 5419, bank157 6858, bank201 9763, bank298 31694, bank362 91474, bank337 91474, bank322 57109] i
  reserve i := ![0, 1, 2, 3, 4, 8, 16, 85, 245, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514727
  seedFloor := 41

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 3807
    · exact rank135 3807
    · exact rank135 4282
    · exact rank134 5419
    · exact rank141 5419
    · exact rank157 6858
    · exact rank201 9763
    · exact rank298 31694
    · exact rank362 91474
    · exact rank337 91474
    · exact rank322 57109
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1321⟩
    · exact ⟨_, cover1322⟩
    · exact ⟨_, cover1323⟩
    · exact ⟨_, cover1324⟩
    · exact ⟨_, cover1325⟩
    · exact ⟨_, cover1326⟩
    · exact ⟨_, cover1327⟩
    · exact ⟨_, cover1330⟩
    · exact ⟨_, cover1333⟩
    · exact ⟨_, cover1332⟩
    · exact ⟨_, cover1331⟩

def price : EarlyPrice := ⟨4, 44, 10, 65/100, 60/100, ![1566847626490, 261453557385, 43644398980, 2975770980], 1003506836008232⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![13336/191, 33931/41, 145866/41, 697268/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.QuarticIntervals4
end Z6969Source1621

-- Source: Research6969.PrefixNearSavedQuarticIntervals4
section Z6969Source1622
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedQuarticIntervals4
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4092,69,827,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.QuarticIntervals4.plan Lower6960.Prefix6969RescueData.QuarticIntervals4.plan Lower6960.Prefix6969RescueData.QuarticIntervals4.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 4 41 44 514727 :=
  ⟨Lower6960.Prefix6969MainCases.QuarticIntervals4.plan, Lower6960.Prefix6969MainCases.QuarticIntervals4.price, Lower6960.Prefix6969MainCases.QuarticIntervals4.valid, Lower6960.Prefix6969MainCases.QuarticIntervals4.priced, Lower6960.Prefix6969MainCases.QuarticIntervals4.sources,
   Lower6960.Prefix6969RescueData.QuarticIntervals4.plan, Lower6960.Prefix6969RescueData.QuarticIntervals4.price, Lower6960.Prefix6969RescueData.QuarticIntervals4.sources, Lower6960.Prefix6969RescueData.QuarticIntervals4.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 210569494450154367 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedQuarticIntervals4
end Z6969Source1622

-- Source: Research6969.PrefixMainDataQuarticIntervals5
section Z6969Source1623
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.QuarticIntervals5
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 10, 15, 14, 18, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank43 2152, bank50 2450, bank54 2755, bank61 2536, bank70 3511, bank85 2903, bank76 4276, bank113 3716, bank140 3997, bank165 6130, bank126 26574, bank199 9241, bank216 10294, bank183 54742, bank174 148759, bank169 292467] i
  head := src1554
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  historyValues := [![16028, 155910, 718633, 3089451],
    ![25417/2, 217623/2, 521808, 2411809],
    ![54680/9, 158210/3, 521808, 1970371],
    ![29433/8, 63933/2, 772256/3, 8506264/9],
    ![64334/25, 544766/25, 204050, 3705625/4],
    ![73988/49, 615752/49, 1050176/9, 4631104/9],
    ![81680/81, 694180/81, 782926/9, 1500625/4],
    ![89110/121, 769170/121, 3487492/49, 303601],
    ![89110/121, 759708/121, 3415612/49, 6431296/25],
    ![89110/121, 759708/121, 3415612/49, 6431296/25],
    ![89110/121, 759708/121, 3415612/49, 6431296/25],
    ![230520/361, 2240600/361, 3224104/49, 6431296/25],
    ![230520/361, 607526/121, 372180/7, 8598824/49],
    ![230520/361, 607526/121, 372180/7, 8598824/49],
    ![984976/1681, 7537584/1681, 657136/15, 113478560/729],
    ![1355575/3362, 7537584/1681, 657136/15, 113478560/729],
    ![1355575/3362, 5502220/1323, 21050998/529, 21383674/147],
    ![1355575/3362, 5508363/1369, 33034736/867, 26491609/196],
    ![954471/2738, 5508363/1369, 33034736/867, 26491609/196],
    ![462882/1369, 5508363/1369, 33034736/867, 26491609/196],
    ![459151/1369, 5508363/1369, 33034736/867, 26491609/196]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 45 514727 := by
  refine ⟨?_, rank154 4628, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1554⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free43_0
    · exact free50_0
    · exact free54_0
    · exact free61_0
    · exact free70_0
    · exact free85_0
    · exact free76_0
    · exact free113_0
    · exact free140_0
    · exact free165_0
    · exact free126_0
    · exact free199_0
    · exact free216_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [290203014, 290116218, 289618583, 289907164, 290078075, 289463400, 290017662, 294620954, 160253510, 160263680, 160274431, 160113907, 85867206, 80045799, 56158550, 78103578, 90570474, 90835054, 114155029, 161185441, 225538278], [1240443, 1240887, 1243433, 1241957, 1241082, 1244227, 1241391, 1217842, 2396400, 2396231, 2396052, 2398721, 4633586, 4982728, 7190719, 5116863, 4386563, 4373221, 3433780, 2380905, 1649317],
  ![119720228727960, 1616158154892, 202984450200, 5220009970], 154453212827618603⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5508363/1369, 33034736/867, 26491609/196] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.QuarticIntervals5
end Z6969Source1623

-- Source: Research6969.PhysicalChecks096
section Z6969Source1624
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1340 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,13,4,1,514727,45⟩
private theorem pass1340_2293 : (Triangular src1340) 2293 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1340_2312 : (Triangular src1340) 2312 2370 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1340_2371 : (Triangular src1340) 2371 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1340 : Cover (Triangular src1340) 2389 2293 [2311,2370,2389] := by
  exact ⟨by decide, by decide, pass1340_2293, by decide, by decide, pass1340_2312, by decide, by decide, pass1340_2371, rfl⟩
def src1341 : Request := ⟨⟨⟨1200,1673,368,13899⟩,52718727069696,218387554859⟩,32,4,1,514727,45⟩
private theorem pass1341_2293 : (Triangular src1341) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1341_2294 : (Triangular src1341) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1341_2297 : (Triangular src1341) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1341_2306 : (Triangular src1341) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1341_2332 : (Triangular src1341) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1341 : Cover (Triangular src1341) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass1341_2293, by decide, by decide, pass1341_2294, by decide, by decide, pass1341_2297, by decide, by decide, pass1341_2306, by decide, by decide, pass1341_2332, rfl⟩
def src1342 : Request := ⟨⟨⟨2100,2928,662,25043⟩,288013660979200,2088662039796⟩,65,4,1,514727,45⟩
private theorem pass1342_2293 : (Triangular src1342) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1342_2300 : (Triangular src1342) 2300 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1342_2320 : (Triangular src1342) 2320 2376 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1342_2377 : (Triangular src1342) 2377 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1342 : Cover (Triangular src1342) 2389 2293 [2299,2319,2376,2389] := by
  exact ⟨by decide, by decide, pass1342_2293, by decide, by decide, pass1342_2300, by decide, by decide, pass1342_2320, by decide, by decide, pass1342_2377, rfl⟩
def src1343 : Request := ⟨⟨⟨5700,7948,1796,64247⟩,5749327563587584,113150499898987⟩,190,4,1,514727,45⟩
private theorem pass1343_2293 : (Triangular src1343) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1343_2301 : (Triangular src1343) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1343_2324 : (Triangular src1343) 2324 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1343_2387 : (Triangular src1343) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1343 : Cover (Triangular src1343) 2389 2293 [2300,2323,2386,2389] := by
  exact ⟨by decide, by decide, pass1343_2293, by decide, by decide, pass1343_2301, by decide, by decide, pass1343_2324, by decide, by decide, pass1343_2387, rfl⟩
def src1344 : Request := ⟨⟨⟨6900,9621,2174,91474⟩,10196763128627200,242895948111878⟩,245,4,1,514727,45⟩
private theorem pass1344_2293 : (Triangular src1344) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1344_2299 : (Triangular src1344) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1344_2316 : (Triangular src1344) 2316 2362 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1344_2363 : (Triangular src1344) 2363 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1344 : Cover (Triangular src1344) 2389 2293 [2298,2315,2362,2389] := by
  exact ⟨by decide, by decide, pass1344_2293, by decide, by decide, pass1344_2299, by decide, by decide, pass1344_2316, by decide, by decide, pass1344_2363, rfl⟩
def src1345 : Request := ⟨⟨⟨275,383,83,3384⟩,635228389376,603020643⟩,0,4,1,514727,49⟩
private theorem pass1345_2293 : (Triangular src1345) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1345_2303 : (Triangular src1345) 2303 2341 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1345_2342 : (Triangular src1345) 2342 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1345 : Cover (Triangular src1345) 2389 2293 [2302,2341,2389] := by
  exact ⟨by decide, by decide, pass1345_2293, by decide, by decide, pass1345_2303, by decide, by decide, pass1345_2342, rfl⟩
def src1346 : Request := ⟨⟨⟨325,453,98,3384⟩,1045036793856,1174588250⟩,1,4,1,514727,49⟩
private theorem pass1346_2293 : (Triangular src1346) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1346_2303 : (Triangular src1346) 2303 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1346_2339 : (Triangular src1346) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1346 : Cover (Triangular src1346) 2389 2293 [2302,2338,2389] := by
  exact ⟨by decide, by decide, pass1346_2293, by decide, by decide, pass1346_2303, by decide, by decide, pass1346_2339, rfl⟩
def src1347 : Request := ⟨⟨⟨325,453,100,3807⟩,1061047500800,1193036697⟩,2,4,1,514727,49⟩
private theorem pass1347_2293 : (Triangular src1347) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1347_2301 : (Triangular src1347) 2301 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1347_2330 : (Triangular src1347) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1347 : Cover (Triangular src1347) 2389 2293 [2300,2329,2389] := by
  exact ⟨by decide, by decide, pass1347_2293, by decide, by decide, pass1347_2301, by decide, by decide, pass1347_2330, rfl⟩
def src1348 : Request := ⟨⟨⟨400,558,123,4282⟩,1971918995456,2734096379⟩,4,4,1,514727,49⟩
private theorem pass1348_2293 : (Triangular src1348) 2293 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1348_2314 : (Triangular src1348) 2314 2384 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1348_2385 : (Triangular src1348) 2385 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1348 : Cover (Triangular src1348) 2389 2293 [2313,2384,2389] := by
  exact ⟨by decide, by decide, pass1348_2293, by decide, by decide, pass1348_2314, by decide, by decide, pass1348_2385, rfl⟩
def src1349 : Request := ⟨⟨⟨470,655,144,6096⟩,3184589537280,5168862572⟩,8,4,1,514727,49⟩
private theorem pass1349_2293 : (Triangular src1349) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1349_2300 : (Triangular src1349) 2300 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1349_2323 : (Triangular src1349) 2323 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1349 : Cover (Triangular src1349) 2389 2293 [2299,2322,2389] := by
  exact ⟨by decide, by decide, pass1349_2293, by decide, by decide, pass1349_2300, by decide, by decide, pass1349_2323, rfl⟩
def src1350 : Request := ⟨⟨⟨690,962,217,7715⟩,10244384358400,24434817260⟩,16,4,1,514727,49⟩
private theorem pass1350_2293 : (Triangular src1350) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1350_2294 : (Triangular src1350) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1350_2297 : (Triangular src1350) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1350_2306 : (Triangular src1350) 2306 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1350_2334 : (Triangular src1350) 2334 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1350 : Cover (Triangular src1350) 2389 2293 [2293,2296,2305,2333,2389] := by
  exact ⟨by decide, by decide, pass1350_2293, by decide, by decide, pass1350_2294, by decide, by decide, pass1350_2297, by decide, by decide, pass1350_2306, by decide, by decide, pass1350_2334, rfl⟩
def src1351 : Request := ⟨⟨⟨1450,2022,445,13899⟩,92998964346880,465769321795⟩,40,4,1,514727,49⟩
private theorem pass1351_2293 : (Triangular src1351) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1351_2294 : (Triangular src1351) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1351_2297 : (Triangular src1351) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1351_2306 : (Triangular src1351) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1351_2332 : (Triangular src1351) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1351 : Cover (Triangular src1351) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass1351_2293, by decide, by decide, pass1351_2294, by decide, by decide, pass1351_2297, by decide, by decide, pass1351_2306, by decide, by decide, pass1351_2332, rfl⟩
def src1354 : Request := ⟨⟨⟨3200,4462,982,35655⟩,997767489781760,11020095796464⟩,110,4,1,514727,49⟩
private theorem pass1354_2293 : (Triangular src1354) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1354_2296 : (Triangular src1354) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1354_2305 : (Triangular src1354) 2305 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1354_2330 : (Triangular src1354) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1354 : Cover (Triangular src1354) 2389 2293 [2295,2304,2329,2389] := by
  exact ⟨by decide, by decide, pass1354_2293, by decide, by decide, pass1354_2296, by decide, by decide, pass1354_2305, by decide, by decide, pass1354_2330, rfl⟩
def src1355 : Request := ⟨⟨⟨3950,5507,1213,50764⟩,1877062482395136,25577387039299⟩,145,4,1,514727,49⟩
private theorem pass1355_2293 : (Triangular src1355) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1355_2297 : (Triangular src1355) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1355_2308 : (Triangular src1355) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1355_2339 : (Triangular src1355) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1355 : Cover (Triangular src1355) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass1355_2293, by decide, by decide, pass1355_2297, by decide, by decide, pass1355_2308, by decide, by decide, pass1355_2339, rfl⟩
def src1356 : Request := ⟨⟨⟨5700,7948,1750,57109⟩,5637370734182400,110890906752819⟩,190,4,1,514727,49⟩
private theorem pass1356_2293 : (Triangular src1356) 2293 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1356_2305 : (Triangular src1356) 2305 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1356_2339 : (Triangular src1356) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1356 : Cover (Triangular src1356) 2389 2293 [2304,2338,2389] := by
  exact ⟨by decide, by decide, pass1356_2293, by decide, by decide, pass1356_2305, by decide, by decide, pass1356_2339, rfl⟩
def src1357 : Request := ⟨⟨⟨6900,9621,2174,72277⟩,10196763128627200,242895948111878⟩,245,4,1,514727,49⟩
private theorem pass1357_2293 : (Triangular src1357) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1357_2300 : (Triangular src1357) 2300 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1357_2319 : (Triangular src1357) 2319 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1357_2372 : (Triangular src1357) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1357 : Cover (Triangular src1357) 2389 2293 [2299,2318,2371,2389] := by
  exact ⟨by decide, by decide, pass1357_2293, by decide, by decide, pass1357_2300, by decide, by decide, pass1357_2319, by decide, by decide, pass1357_2372, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1624

-- Source: Research6969.PrefixRescueDataQuarticIntervals5
section Z6969Source1625
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals5
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,48⟩
  bank i := ![bank100 3384, bank101 3807, bank134 3807, bank134 4282, bank134 5419, bank142 5419, bank193 7715, bank224 13899, bank248 25043, bank337 64247, bank350 91474] i
  reserve i := ![0, 1, 2, 3, 4, 6, 13, 32, 65, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514727
  seedFloor := 45

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank100 3384
    · exact rank101 3807
    · exact rank134 3807
    · exact rank134 4282
    · exact rank134 5419
    · exact rank142 5419
    · exact rank193 7715
    · exact rank224 13899
    · exact rank248 25043
    · exact rank337 64247
    · exact rank350 91474
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1334⟩
    · exact ⟨_, cover1335⟩
    · exact ⟨_, cover1336⟩
    · exact ⟨_, cover1337⟩
    · exact ⟨_, cover1338⟩
    · exact ⟨_, cover1339⟩
    · exact ⟨_, cover1340⟩
    · exact ⟨_, cover1341⟩
    · exact ⟨_, cover1342⟩
    · exact ⟨_, cover1343⟩
    · exact ⟨_, cover1344⟩

def price : EarlyPrice := ⟨4, 48, 10, 65/100, 70/100, ![1709288286544, 245986171522, 40623485744, 2538981990], 903080956871157⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5381/82, 150455/191, 638492/191, 3083856/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.QuarticIntervals5
end Z6969Source1625

-- Source: Research6969.PrefixNearSavedQuarticIntervals5
section Z6969Source1626
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedQuarticIntervals5
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4023,65,787,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.QuarticIntervals5.plan Lower6960.Prefix6969RescueData.QuarticIntervals5.plan Lower6960.Prefix6969RescueData.QuarticIntervals5.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 4 45 48 514727 :=
  ⟨Lower6960.Prefix6969MainCases.QuarticIntervals5.plan, Lower6960.Prefix6969MainCases.QuarticIntervals5.price, Lower6960.Prefix6969MainCases.QuarticIntervals5.valid, Lower6960.Prefix6969MainCases.QuarticIntervals5.priced, Lower6960.Prefix6969MainCases.QuarticIntervals5.sources,
   Lower6960.Prefix6969RescueData.QuarticIntervals5.plan, Lower6960.Prefix6969RescueData.QuarticIntervals5.price, Lower6960.Prefix6969RescueData.QuarticIntervals5.sources, Lower6960.Prefix6969RescueData.QuarticIntervals5.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 212097224644355866 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedQuarticIntervals5
end Z6969Source1626

-- Source: Research6969.PrefixMainDataQuarticIntervals6
section Z6969Source1627
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.QuarticIntervals6
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 9, 10, 10, 16, 13, 17, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank35 2061, bank44 2409, bank51 2810, bank47 3362, bank56 2591, bank67 3891, bank72 2841, bank97 3273, bank116 3644, bank140 3997, bank161 6246, bank128 25826, bank206 8864, bank214 10456, bank186 46700, bank174 148759, bank169 292467] i
  head := src1555
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  historyValues := [![15952, 156008, 716854, 3123392],
    ![25417/2, 107313, 521808, 2411809],
    ![54680/9, 156050/3, 521808, 3802799/2],
    ![29433/8, 252249/8, 761780/3, 8208508/9],
    ![5710/3, 286835/18, 325051/2, 4602213/8],
    ![18775/16, 81895/8, 118514, 10758594/25],
    ![20312/25, 370597/50, 561779/6, 3137365/9],
    ![80228/121, 835034/121, 3770022/49, 3137365/9],
    ![80228/121, 748624/121, 3375780/49, 6713281/25],
    ![80228/121, 748624/121, 3375780/49, 6713281/25],
    ![80228/121, 748624/121, 3375780/49, 6713281/25],
    ![80228/121, 166424/27, 62262, 10712529/49],
    ![80228/121, 596920/121, 2576676/49, 1162436/7],
    ![80228/121, 596920/121, 2576676/49, 1162436/7],
    ![961376/1681, 7409208/1681, 1092356/25, 12397616/81],
    ![33193/82, 7409208/1681, 1092356/25, 12397616/81],
    ![33193/82, 5416468/1323, 73240044/1849, 2827616/21],
    ![33193/82, 5424048/1369, 9180368/243, 2827616/21],
    ![481425/1369, 5424048/1369, 9180368/243, 2827616/21],
    ![462882/1369, 5424048/1369, 9180368/243, 2827616/21],
    ![459151/1369, 5424048/1369, 9180368/243, 2827616/21]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 49 514727 := by
  refine ⟨?_, rank154 4466, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1555⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free35_0
    · exact free44_0
    · exact free51_0
    · exact free47_0
    · exact free56_0
    · exact free67_0
    · exact free72_0
    · exact free97_0
    · exact free116_1
    · exact free140_0
    · exact free161_0
    · exact free128_0
    · exact free206_0
    · exact free214_0
    · exact free186_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [287023628, 286150574, 286768028, 286178055, 286267822, 286483585, 286619874, 293437860, 159759927, 159847434, 159930529, 159511487, 57583779, 74962701, 55095706, 78268318, 90834758, 90789857, 113966299, 160541469, 225045270], [1256708, 1261175, 1258016, 1261034, 1260575, 1259471, 1258774, 1223894, 2404606, 2403152, 2401770, 2408737, 7007659, 5333782, 7330713, 5105486, 4373236, 4375500, 3440332, 2391612, 1653371],
  ![119458530221400, 1616691060900, 202540743000, 5207595720], 152972030711806733⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5424048/1369, 9180368/243, 2827616/21] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.QuarticIntervals6
end Z6969Source1627

-- Source: Research6969.PrefixRescueDataQuarticIntervals6
section Z6969Source1628
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals6
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,52⟩
  bank i := ![bank78 3384, bank100 3384, bank101 3807, bank134 4282, bank142 6096, bank194 7715, bank233 13899, bank296 35655, bank350 72277, bank336 57109, bank306 50764] i
  reserve i := ![0, 1, 2, 4, 8, 16, 40, 110, 245, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514727
  seedFloor := 49

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank78 3384
    · exact rank100 3384
    · exact rank101 3807
    · exact rank134 4282
    · exact rank142 6096
    · exact rank194 7715
    · exact rank233 13899
    · exact rank296 35655
    · exact rank350 72277
    · exact rank336 57109
    · exact rank306 50764
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1345⟩
    · exact ⟨_, cover1346⟩
    · exact ⟨_, cover1347⟩
    · exact ⟨_, cover1348⟩
    · exact ⟨_, cover1349⟩
    · exact ⟨_, cover1350⟩
    · exact ⟨_, cover1351⟩
    · exact ⟨_, cover1354⟩
    · exact ⟨_, cover1357⟩
    · exact ⟨_, cover1356⟩
    · exact ⟨_, cover1355⟩

def price : EarlyPrice := ⟨4, 52, 10, 65/100, 60/100, ![1463119717879, 235162535614, 44008775498, 2538981990], 841779139911467⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![4573/73, 61775/82, 394700/123, 1879202/123] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.QuarticIntervals6
end Z6969Source1628

-- Source: Research6969.PrefixNearSavedQuarticIntervals6
section Z6969Source1629
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedQuarticIntervals6
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,3962,62,753,true⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.QuarticIntervals6.plan Lower6960.Prefix6969RescueData.QuarticIntervals6.plan Lower6960.Prefix6969RescueData.QuarticIntervals6.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  exact ⟨by decide, by decide +kernel⟩

def data : NearCase 4 49 52 514727 :=
  ⟨Lower6960.Prefix6969MainCases.QuarticIntervals6.plan, Lower6960.Prefix6969MainCases.QuarticIntervals6.price, Lower6960.Prefix6969MainCases.QuarticIntervals6.valid, Lower6960.Prefix6969MainCases.QuarticIntervals6.priced, Lower6960.Prefix6969MainCases.QuarticIntervals6.sources,
   Lower6960.Prefix6969RescueData.QuarticIntervals6.plan, Lower6960.Prefix6969RescueData.QuarticIntervals6.price, Lower6960.Prefix6969RescueData.QuarticIntervals6.sources, Lower6960.Prefix6969RescueData.QuarticIntervals6.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 208838473869358440 := by
  unfold NearCase.fee
  unfold Exit.extra
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedQuarticIntervals6
end Z6969Source1629

-- Source: Research6969.PrefixMainDataQuarticIntervals7
section Z6969Source1630
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.QuarticIntervals7
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 10, 15, 18, 16, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank19 1656, bank24 1838, bank31 1925, bank43 2152, bank50 2450, bank54 2755, bank61 2536, bank70 3511, bank87 3887, bank95 3103, bank116 3644, bank140 3997, bank165 6130, bank129 24535, bank206 8864, bank214 10456, bank186 46700, bank174 148759, bank169 292467] i
  head := src1556
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  historyValues := [![16153, 154560, 711786, 3025922],
    ![25417/2, 211999/2, 521808, 2411809],
    ![6218, 458804/9, 518512, 1790136],
    ![29433/8, 62299/2, 2257792/9, 7947512/9],
    ![64334/25, 530478/25, 204050, 7947512/9],
    ![73988/49, 599336/49, 1050176/9, 4631104/9],
    ![81680/81, 675940/81, 254186/3, 1500625/4],
    ![89110/121, 749410/121, 3398116/49, 303601],
    ![89110/121, 738124/121, 3319852/49, 6431296/25],
    ![89110/121, 738124/121, 3319852/49, 6431296/25],
    ![243680/361, 2099900/361, 3094052/49, 15108769/64],
    ![243680/361, 2099900/361, 3094052/49, 26834744/121],
    ![243680/361, 588542/121, 2539472/49, 13278736/81],
    ![243680/361, 588542/121, 2539472/49, 13278736/81],
    ![984976/1681, 7316272/1681, 657136/15, 9394225/64],
    ![33263/82, 7316272/1681, 657136/15, 9394225/64],
    ![33263/82, 1780024/441, 72216792/1849, 19163968/147],
    ![33263/82, 5350492/1369, 9180368/243, 19163968/147],
    ![481425/1369, 5350492/1369, 9180368/243, 19163968/147],
    ![462882/1369, 5350492/1369, 9180368/243, 19163968/147],
    ![459151/1369, 5350492/1369, 9180368/243, 19163968/147]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 53 514727 := by
  refine ⟨?_, rank154 4324, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1556⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free19_0
    · exact free24_0
    · exact free31_0
    · exact free43_0
    · exact free50_0
    · exact free54_0
    · exact free61_0
    · exact free70_0
    · exact free87_0
    · exact free95_0
    · exact free116_1
    · exact free140_0
    · exact free165_0
    · exact free129_0
    · exact free206_0
    · exact free214_0
    · exact free186_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [283894312, 283525699, 282532401, 281758090, 283684831, 282459547, 282580234, 287017247, 158603070, 158632497, 158453346, 158355639, 55719909, 73650207, 54646780, 79369888, 92402818, 92114352, 113739882, 160315052, 224868821], [1272717, 1274603, 1279684, 1283646, 1273789, 1280057, 1279440, 1256741, 2423841, 2423351, 2426330, 2427955, 7247060, 5436001, 7394690, 5029408, 4294164, 4308710, 3448192, 2395377, 1654822],
  ![119364867563220, 1616881822204, 202381938900, 5129996160], 150993239094514072⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5350492/1369, 9180368/243, 19163968/147] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.QuarticIntervals7
end Z6969Source1630

-- Source: Research6969.PrefixRescueDataQuarticIntervals7
section Z6969Source1631
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals7
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,56⟩
  bank i := ![bank80 2674, bank100 3008, bank100 3384, bank102 3807, bank134 3807, bank134 4817, bank143 4817, bank193 6858, bank218 13899, bank234 17590, bank320 57109] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 16, 32, 50, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514727
  seedFloor := 53

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank80 2674
    · exact rank100 3008
    · exact rank100 3384
    · exact rank102 3807
    · exact rank134 3807
    · exact rank134 4817
    · exact rank143 4817
    · exact rank193 6858
    · exact rank218 13899
    · exact rank234 17590
    · exact rank320 57109
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1358⟩
    · exact ⟨_, cover1359⟩
    · exact ⟨_, cover1360⟩
    · exact ⟨_, cover1361⟩
    · exact ⟨_, cover1362⟩
    · exact ⟨_, cover1363⟩
    · exact ⟨_, cover1364⟩
    · exact ⟨_, cover1365⟩
    · exact ⟨_, cover1366⟩
    · exact ⟨_, cover1367⟩
    · exact ⟨_, cover1368⟩

def price : EarlyPrice := ⟨4, 56, 10, 60/100, 50/100, ![1244998929382, 179622806105, 32962201776, 1765842120], 707946607197812⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![11228/191, 141781/191, 603188/191, 16744] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.QuarticIntervals7
end Z6969Source1631

end Merged_Z6969Pack0713

-- merged module Z6969Pack0714
section Merged_Z6969Pack0714

-- Source: Research6969.PrefixNearSavedQuarticIntervals7
section Z6969Source1632
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedQuarticIntervals7
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,3908,58,742,true⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.QuarticIntervals7.plan Lower6960.Prefix6969RescueData.QuarticIntervals7.plan Lower6960.Prefix6969RescueData.QuarticIntervals7.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  exact ⟨by decide, by decide +kernel⟩

def data : NearCase 4 53 56 514727 :=
  ⟨Lower6960.Prefix6969MainCases.QuarticIntervals7.plan, Lower6960.Prefix6969MainCases.QuarticIntervals7.price, Lower6960.Prefix6969MainCases.QuarticIntervals7.valid, Lower6960.Prefix6969MainCases.QuarticIntervals7.priced, Lower6960.Prefix6969MainCases.QuarticIntervals7.sources,
   Lower6960.Prefix6969RescueData.QuarticIntervals7.plan, Lower6960.Prefix6969RescueData.QuarticIntervals7.price, Lower6960.Prefix6969RescueData.QuarticIntervals7.sources, Lower6960.Prefix6969RescueData.QuarticIntervals7.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 199152367227150730 := by
  unfold NearCase.fee
  unfold Exit.extra
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedQuarticIntervals7
end Z6969Source1632

-- Source: Research6969.PrefixNearSelect4
section Z6969Source1633
set_option autoImplicit true
namespace Lower6960.Prefix6969Early
set_option maxHeartbeats 8000000

theorem nearChoose4 (j : Fin 56) (ok : UniformAllowed 4 (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧ w≤514727 ∧ ∃ c : NearCase 4 l u w, c.uniform := by
  fin_cases j
  · refine ⟨1, 1, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases2.fee_exact]; decide +kernel
  · refine ⟨2, 3, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases3.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases3.fee_exact]; decide +kernel
  · refine ⟨2, 3, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases3.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases3.fee_exact]; decide +kernel
  · refine ⟨4, 8, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases4.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases4.fee_exact]; decide +kernel
  · refine ⟨4, 8, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases4.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases4.fee_exact]; decide +kernel
  · refine ⟨4, 8, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases4.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases4.fee_exact]; decide +kernel
  · refine ⟨4, 8, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases4.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases4.fee_exact]; decide +kernel
  · refine ⟨4, 8, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases4.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases4.fee_exact]; decide +kernel
  · refine ⟨9, 15, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases5.fee_exact]; decide +kernel
  · refine ⟨9, 15, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases5.fee_exact]; decide +kernel
  · refine ⟨9, 15, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases5.fee_exact]; decide +kernel
  · refine ⟨9, 15, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases5.fee_exact]; decide +kernel
  · refine ⟨9, 15, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases5.fee_exact]; decide +kernel
  · refine ⟨9, 15, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases5.fee_exact]; decide +kernel
  · refine ⟨9, 15, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases5.fee_exact]; decide +kernel
  · refine ⟨16, 25, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases6.fee_exact]; decide +kernel
  · refine ⟨16, 25, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases6.fee_exact]; decide +kernel
  · refine ⟨16, 25, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases6.fee_exact]; decide +kernel
  · refine ⟨16, 25, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases6.fee_exact]; decide +kernel
  · refine ⟨16, 25, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases6.fee_exact]; decide +kernel
  · refine ⟨16, 25, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases6.fee_exact]; decide +kernel
  · refine ⟨16, 25, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases6.fee_exact]; decide +kernel
  · refine ⟨16, 25, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases6.fee_exact]; decide +kernel
  · refine ⟨16, 25, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases6.fee_exact]; decide +kernel
  · refine ⟨16, 25, 514727, by decide, by decide, by decide, NearSavedHigherHelperCases6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases6.fee_exact]; decide +kernel
  · refine ⟨26, 29, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals0.fee_exact]; decide +kernel
  · refine ⟨26, 29, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals0.fee_exact]; decide +kernel
  · refine ⟨26, 29, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals0.fee_exact]; decide +kernel
  · refine ⟨26, 29, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals0.fee_exact]; decide +kernel
  · refine ⟨30, 33, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals1.fee_exact]; decide +kernel
  · refine ⟨30, 33, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals1.fee_exact]; decide +kernel
  · refine ⟨30, 33, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals1.fee_exact]; decide +kernel
  · refine ⟨30, 33, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals1.fee_exact]; decide +kernel
  · refine ⟨34, 37, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals2.fee_exact]; decide +kernel
  · refine ⟨34, 37, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals2.fee_exact]; decide +kernel
  · refine ⟨34, 37, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals2.fee_exact]; decide +kernel
  · refine ⟨34, 37, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals2.fee_exact]; decide +kernel
  · refine ⟨38, 40, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals3.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals3.fee_exact]; decide +kernel
  · refine ⟨38, 40, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals3.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals3.fee_exact]; decide +kernel
  · refine ⟨38, 40, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals3.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals3.fee_exact]; decide +kernel
  · refine ⟨41, 44, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals4.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals4.fee_exact]; decide +kernel
  · refine ⟨41, 44, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals4.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals4.fee_exact]; decide +kernel
  · refine ⟨41, 44, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals4.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals4.fee_exact]; decide +kernel
  · refine ⟨41, 44, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals4.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals4.fee_exact]; decide +kernel
  · refine ⟨45, 48, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals5.fee_exact]; decide +kernel
  · refine ⟨45, 48, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals5.fee_exact]; decide +kernel
  · refine ⟨45, 48, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals5.fee_exact]; decide +kernel
  · refine ⟨45, 48, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals5.fee_exact]; decide +kernel
  · refine ⟨49, 52, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals6.fee_exact]; decide +kernel
  · refine ⟨49, 52, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals6.fee_exact]; decide +kernel
  · refine ⟨49, 52, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals6.fee_exact]; decide +kernel
  · refine ⟨49, 52, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals6.fee_exact]; decide +kernel
  · refine ⟨53, 56, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals7.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals7.fee_exact]; decide +kernel
  · refine ⟨53, 56, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals7.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals7.fee_exact]; decide +kernel
  · refine ⟨53, 56, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals7.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals7.fee_exact]; decide +kernel
  · refine ⟨53, 56, 514727, by decide, by decide, by decide, NearSavedQuarticIntervals7.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedQuarticIntervals7.fee_exact]; decide +kernel

end Lower6960.Prefix6969Early
end Z6969Source1633

-- Source: Research6969.PrefixMainDataHigherHelperCases10
section Z6969Source1634
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases10
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 8, 12, 18, 21, 21, 40, 65, 75, 75] i
  bank i := ![bank3 1490, bank10 1603, bank24 1838, bank37 2039, bank50 2450, bank63 2899, bank89 3732, bank123 3616, bank83 5597, bank147 6388, bank158 51722, bank211 10626, bank171 201573] i
  head := src1681
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15640, 166868, 770013, 3583539],
    ![24861/2, 252139/2, 1149893/2, 5160057/2],
    ![29433/8, 294647/8, 2667908/9, 3944348/3],
    ![17323/9, 168742/9, 1517767/8, 6563541/8],
    ![81680/81, 802780/81, 904196/9, 1314425/3],
    ![81680/81, 802780/81, 904196/9, 1314425/3],
    ![250508/361, 2453472/361, 11054244/169, 48053232/169],
    ![250508/361, 715336/121, 60568, 15519872/75],
    ![254619/484, 715336/121, 60568, 15519872/75],
    ![254619/484, 538667/100, 2423914/49, 15519872/75],
    ![480716/1323, 538667/100, 2423914/49, 15519872/75],
    ![480716/1323, 25443684/5329, 26926284/625, 112911876/625],
    ![1826342/5329, 25443684/5329, 26926284/625, 112911876/625]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 5 9 643409 := by
  refine ⟨?_, rank154 6438, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1681⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free24_0
    · exact free37_0
    · exact free50_0
    · exact free63_0
    · exact free89_0
    · exact free123_0
    · exact free83_1
    · exact free147_0
    · exact free158_0
    · exact free211_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [332047066, 331517077, 330499655, 330435805, 148383232, 148366630, 148490619, 36646026, 68969432, 97123150, 103853873, 144629835, 236374885], [1036464, 1037916, 1040705, 1040880, 2593759, 2594035, 2591973, 11122143, 5817933, 4076070, 3791999, 2668432, 1560221],
  ![125472516455700, 1604451633560, 212737396500, 4512478810], 183397136016856618⟩

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

theorem final_cap : plan.history plan.last = ![1826342/5329, 25443684/5329, 26926284/625, 112911876/625] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases10
end Z6969Source1634

-- Source: Research6969.PhysicalChecks102
section Z6969Source1635
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1462 : Request := ⟨⟨⟨3950,5510,1189,102908⟩,1848744952463360,25226292539926⟩,85,5,1,643409,4⟩
private theorem pass1462_2293 : (Triangular src1462) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1462_2294 : (Triangular src1462) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1462_2297 : (Triangular src1462) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1462_2305 : (Triangular src1462) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1462_2327 : (Triangular src1462) 2327 2388 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1462_2389 : (Triangular src1462) 2389 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1462 : Cover (Triangular src1462) 2389 2293 [2293,2296,2304,2326,2388,2389] := by
  exact ⟨by decide, by decide, pass1462_2293, by decide, by decide, pass1462_2294, by decide, by decide, pass1462_2297, by decide, by decide, pass1462_2305, by decide, by decide, pass1462_2327, by decide, by decide, pass1462_2389, rfl⟩
def src1463 : Request := ⟨⟨⟨3200,4462,982,264035⟩,997767489781760,11020095796464⟩,110,5,1,643409,4⟩
private theorem pass1463_2293 : (Triangular src1463) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1463_2302 : (Triangular src1463) 2302 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1463_2327 : (Triangular src1463) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1463 : Cover (Triangular src1463) 2389 2293 [2301,2326,2389] := by
  exact ⟨by decide, by decide, pass1463_2293, by decide, by decide, pass1463_2302, by decide, by decide, pass1463_2327, rfl⟩
def src1464 : Request := ⟨⟨⟨8300,11577,2548,208621⟩,17399709518790656,498847383098023⟩,190,5,1,643409,4⟩
private theorem pass1464_2293 : (Triangular src1464) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1464_2297 : (Triangular src1464) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1464_2308 : (Triangular src1464) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1464_2339 : (Triangular src1464) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1464 : Cover (Triangular src1464) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass1464_2293, by decide, by decide, pass1464_2297, by decide, by decide, pass1464_2308, by decide, by decide, pass1464_2339, rfl⟩
def src1465 : Request := ⟨⟨⟨400,558,123,9763⟩,1971918995456,2734096379⟩,0,5,1,643409,9⟩
private theorem pass1465_2293 : (Triangular src1465) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1465_2299 : (Triangular src1465) 2299 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1465_2319 : (Triangular src1465) 2319 2385 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1465_2386 : (Triangular src1465) 2386 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1465 : Cover (Triangular src1465) 2389 2293 [2298,2318,2385,2389] := by
  exact ⟨by decide, by decide, pass1465_2293, by decide, by decide, pass1465_2299, by decide, by decide, pass1465_2319, by decide, by decide, pass1465_2386, rfl⟩
def src1466 : Request := ⟨⟨⟨470,655,141,10983⟩,3134317133824,5085275599⟩,1,5,1,643409,9⟩
private theorem pass1466_2293 : (Triangular src1466) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1466_2300 : (Triangular src1466) 2300 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1466_2324 : (Triangular src1466) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1466 : Cover (Triangular src1466) 2389 2293 [2299,2323,2389] := by
  exact ⟨by decide, by decide, pass1466_2293, by decide, by decide, pass1466_2300, by decide, by decide, pass1466_2324, rfl⟩
def src1467 : Request := ⟨⟨⟨470,655,141,13899⟩,3134317133824,5085275599⟩,3,5,1,643409,9⟩
private theorem pass1467_2293 : (Triangular src1467) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1467_2294 : (Triangular src1467) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1467_2297 : (Triangular src1467) 2297 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1467_2307 : (Triangular src1467) 2307 2339 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1467_2340 : (Triangular src1467) 2340 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1467 : Cover (Triangular src1467) 2389 2293 [2293,2296,2306,2339,2389] := by
  exact ⟨by decide, by decide, pass1467_2293, by decide, by decide, pass1467_2294, by decide, by decide, pass1467_2297, by decide, by decide, pass1467_2307, by decide, by decide, pass1467_2340, rfl⟩
def src1468 : Request := ⟨⟨⟨690,962,212,17590⟩,10065769922560,23997864317⟩,8,5,1,643409,9⟩
private theorem pass1468_2293 : (Triangular src1468) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1468_2303 : (Triangular src1468) 2303 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1468_2334 : (Triangular src1468) 2334 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1468 : Cover (Triangular src1468) 2389 2293 [2302,2333,2389] := by
  exact ⟨by decide, by decide, pass1468_2293, by decide, by decide, pass1468_2303, by decide, by decide, pass1468_2334, rfl⟩
def src1469 : Request := ⟨⟨⟨1200,1673,368,35655⟩,52718727069696,218387554859⟩,25,5,1,643409,9⟩
private theorem pass1469_2293 : (Triangular src1469) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1469_2296 : (Triangular src1469) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1469_2304 : (Triangular src1469) 2304 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1469_2328 : (Triangular src1469) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1469 : Cover (Triangular src1469) 2389 2293 [2295,2303,2327,2389] := by
  exact ⟨by decide, by decide, pass1469_2293, by decide, by decide, pass1469_2296, by decide, by decide, pass1469_2304, by decide, by decide, pass1469_2328, rfl⟩
def src1470 : Request := ⟨⟨⟨2100,2929,645,45124⟩,282396798484480,2049139102608⟩,40,5,1,643409,9⟩
private theorem pass1470_2293 : (Triangular src1470) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1470_2295 : (Triangular src1470) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1470_2301 : (Triangular src1470) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1470_2318 : (Triangular src1470) 2318 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1470_2366 : (Triangular src1470) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1470 : Cover (Triangular src1470) 2389 2293 [2294,2300,2317,2365,2389] := by
  exact ⟨by decide, by decide, pass1470_2293, by decide, by decide, pass1470_2295, by decide, by decide, pass1470_2301, by decide, by decide, pass1470_2318, by decide, by decide, pass1470_2366, rfl⟩
def src1473 : Request := ⟨⟨⟨2600,3625,798,164837⟩,535425056505856,4803689494279⟩,85,5,1,643409,9⟩
private theorem pass1473_2293 : (Triangular src1473) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1473_2306 : (Triangular src1473) 2306 2341 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1473_2342 : (Triangular src1473) 2342 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1473 : Cover (Triangular src1473) 2389 2293 [2305,2341,2389] := by
  exact ⟨by decide, by decide, pass1473_2293, by decide, by decide, pass1473_2306, by decide, by decide, pass1473_2342, rfl⟩
def src1474 : Request := ⟨⟨⟨4800,6692,1474,857398⟩,3367547627110400,55757027345056⟩,190,5,1,643409,9⟩
private theorem pass1474_2293 : (Triangular src1474) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1474_2295 : (Triangular src1474) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1474_2300 : (Triangular src1474) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1474_2314 : (Triangular src1474) 2314 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1474_2353 : (Triangular src1474) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1474 : Cover (Triangular src1474) 2389 2293 [2294,2299,2313,2352,2389] := by
  exact ⟨by decide, by decide, pass1474_2293, by decide, by decide, pass1474_2295, by decide, by decide, pass1474_2300, by decide, by decide, pass1474_2314, by decide, by decide, pass1474_2353, rfl⟩
def src1475 : Request := ⟨⟨⟨10000,13948,3070,234698⟩,30428373265940480,1050983571587703⟩,245,5,1,643409,9⟩
private theorem pass1475_2293 : (Triangular src1475) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1475_2299 : (Triangular src1475) 2299 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1475_2315 : (Triangular src1475) 2315 2358 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1475_2359 : (Triangular src1475) 2359 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1475 : Cover (Triangular src1475) 2389 2293 [2298,2314,2358,2389] := by
  exact ⟨by decide, by decide, pass1475_2293, by decide, by decide, pass1475_2299, by decide, by decide, pass1475_2315, by decide, by decide, pass1475_2359, rfl⟩
def src1478 : Request := ⟨⟨⟨400,558,123,7715⟩,1971918995456,2734096379⟩,0,5,1,643409,16⟩
private theorem pass1478_2293 : (Triangular src1478) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1478_2298 : (Triangular src1478) 2298 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1478_2315 : (Triangular src1478) 2315 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1478_2372 : (Triangular src1478) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1478 : Cover (Triangular src1478) 2389 2293 [2297,2314,2371,2389] := by
  exact ⟨by decide, by decide, pass1478_2293, by decide, by decide, pass1478_2298, by decide, by decide, pass1478_2315, by decide, by decide, pass1478_2372, rfl⟩
def src1479 : Request := ⟨⟨⟨470,655,141,8679⟩,3134317133824,5085275599⟩,1,5,1,643409,16⟩
private theorem pass1479_2293 : (Triangular src1479) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1479_2298 : (Triangular src1479) 2298 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1479_2314 : (Triangular src1479) 2314 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1479_2367 : (Triangular src1479) 2367 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1479 : Cover (Triangular src1479) 2389 2293 [2297,2313,2366,2389] := by
  exact ⟨by decide, by decide, pass1479_2293, by decide, by decide, pass1479_2298, by decide, by decide, pass1479_2314, by decide, by decide, pass1479_2367, rfl⟩
def src1480 : Request := ⟨⟨⟨470,655,141,9763⟩,3134317133824,5085275599⟩,2,5,1,643409,16⟩
private theorem pass1480_2293 : (Triangular src1480) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1480_2298 : (Triangular src1480) 2298 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1480_2314 : (Triangular src1480) 2314 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1480_2367 : (Triangular src1480) 2367 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1480 : Cover (Triangular src1480) 2389 2293 [2297,2313,2366,2389] := by
  exact ⟨by decide, by decide, pass1480_2293, by decide, by decide, pass1480_2298, by decide, by decide, pass1480_2314, by decide, by decide, pass1480_2367, rfl⟩
def src1481 : Request := ⟨⟨⟨560,781,169,10983⟩,5316921262080,10299257375⟩,4,5,1,643409,16⟩
private theorem pass1481_2293 : (Triangular src1481) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1481_2297 : (Triangular src1481) 2297 2309 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1481_2310 : (Triangular src1481) 2310 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1481_2351 : (Triangular src1481) 2351 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1481 : Cover (Triangular src1481) 2389 2293 [2296,2309,2350,2389] := by
  exact ⟨by decide, by decide, pass1481_2293, by decide, by decide, pass1481_2297, by decide, by decide, pass1481_2310, by decide, by decide, pass1481_2351, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1635

-- Source: Research6969.PrefixRescueDataHigherHelperCases10
section Z6969Source1636
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases10
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,5,1,15⟩
  bank i := ![bank134 9763, bank141 10983, bank141 13899, bank193 17590, bank224 35655, bank249 45124, bank262 164837, bank375 234698, bank319 857398, bank375 234698] i
  reserve i := ![0, 1, 3, 8, 25, 40, 85, 245, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643409
  seedFloor := 9

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank134 9763
    · exact rank141 10983
    · exact rank141 13899
    · exact rank193 17590
    · exact rank224 35655
    · exact rank249 45124
    · exact rank262 164837
    · exact rank375 234698
    · exact rank319 857398
    · exact rank375 234698
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1465⟩
    · exact ⟨_, cover1466⟩
    · exact ⟨_, cover1467⟩
    · exact ⟨_, cover1468⟩
    · exact ⟨_, cover1469⟩
    · exact ⟨_, cover1470⟩
    · exact ⟨_, cover1473⟩
    · exact ⟨_, cover1475⟩
    · exact ⟨_, cover1474⟩
    · exact ⟨_, cover1475⟩

def price : EarlyPrice := ⟨5, 15, 9, 85/100, 70/100, ![5006686451608, 1365591271172, 17926945720, 4780536460], 2976009722510187⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![12588/191, 140374/123, 691355/123, 586745/41] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases10
end Z6969Source1636

-- Source: Research6969.PrefixNearSavedHigherHelperCases10
section Z6969Source1637
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases10
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4774,65,1141,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases10.plan Lower6960.Prefix6969RescueData.HigherHelperCases10.plan Lower6960.Prefix6969RescueData.HigherHelperCases10.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 5 9 15 643409 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases10.plan, Lower6960.Prefix6969MainCases.HigherHelperCases10.price, Lower6960.Prefix6969MainCases.HigherHelperCases10.valid, Lower6960.Prefix6969MainCases.HigherHelperCases10.priced, Lower6960.Prefix6969MainCases.HigherHelperCases10.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases10.plan, Lower6960.Prefix6969RescueData.HigherHelperCases10.price, Lower6960.Prefix6969RescueData.HigherHelperCases10.sources, Lower6960.Prefix6969RescueData.HigherHelperCases10.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 207456154989119689 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases10
end Z6969Source1637

-- Source: Research6969.PrefixMainDataHigherHelperCases11
section Z6969Source1638
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases11
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 75, 105, 75, 75] i
  bank i := ![bank3 1490, bank10 1603, bank19 1656, bank24 1838, bank28 2005, bank37 2039, bank42 2497, bank52 2900, bank65 3612, bank83 5597, bank83 2752, bank123 3616, bank122 24063, bank159 6076, bank199 9241, bank187 32183, bank230 14067, bank172 88577, bank171 201573] i
  head := src1682
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14995, 163708, 755097, 3627573],
    ![24861/2, 244039/2, 556384, 2569609],
    ![6218, 175676/3, 556384, 2479032],
    ![29433/8, 71243/2, 2580608/9, 3668648/3],
    ![62542/25, 616298/25, 411025/2, 4020025/4],
    ![17323/9, 326009/18, 366673/2, 3052383/4],
    ![36739/32, 373921/32, 1203554/9, 14952036/25],
    ![86036/121, 870244/121, 3933404/49, 17365200/49],
    ![86036/121, 870244/121, 3933404/49, 17365200/49],
    ![254619/484, 2944892/441, 3328102/49, 17365200/49],
    ![254619/484, 2944892/441, 3328102/49, 8239488/25],
    ![254619/484, 62576/11, 60568, 204304],
    ![41249/100, 62576/11, 60568, 204304],
    ![41249/100, 104041/20, 48422, 188356],
    ![41249/100, 6195820/1323, 5232894/121, 41501331/242],
    ![1960504/5329, 6195820/1323, 5232894/121, 41501331/242],
    ![1960504/5329, 231995/51, 370360/9, 1299895/8],
    ![1872696/5329, 231995/51, 370360/9, 1299895/8],
    ![1826342/5329, 231995/51, 370360/9, 1299895/8]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 5 16 643409 := by
  refine ⟨?_, rank154 5988, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1682⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free19_0
    · exact free24_0
    · exact free28_0
    · exact free37_0
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free83_1
    · exact free83_0
    · exact free123_0
    · exact free122_0
    · exact free159_0
    · exact free199_0
    · exact free187_0
    · exact free230_0
    · exact free172_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [316708766, 316345251, 315656929, 315717926, 315387921, 314963438, 316103421, 147449300, 147453511, 147289335, 147337548, 71621464, 71628157, 83000186, 88488764, 123742077, 100725873, 138974961, 233896006], [1104846, 1106705, 1110226, 1109914, 1111603, 1113774, 1107942, 2609287, 2609217, 2611946, 2611145, 5597240, 5596708, 4803829, 4491538, 3158899, 3924016, 2792414, 1580602],
  ![124156677904920, 1607129637344, 210506405400, 5370128300], 173546922628628332⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 231995/51, 370360/9, 1299895/8] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases11
end Z6969Source1638

-- Source: Research6969.PrefixRescueDataHigherHelperCases11
section Z6969Source1639
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases11
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,25⟩
  bank i := ![bank134 7715, bank141 8679, bank141 9763, bank155 10983, bank193 13899, bank222 19788, bank242 40111, bank262 130242, bank338 115771, bank319 677451, bank375 185441] i
  reserve i := ![0, 1, 2, 4, 8, 16, 40, 85, 145, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643409
  seedFloor := 16

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank134 7715
    · exact rank141 8679
    · exact rank141 9763
    · exact rank155 10983
    · exact rank193 13899
    · exact rank222 19788
    · exact rank242 40111
    · exact rank262 130242
    · exact rank338 115771
    · exact rank319 677451
    · exact rank375 185441
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1478⟩
    · exact ⟨_, cover1479⟩
    · exact ⟨_, cover1480⟩
    · exact ⟨_, cover1481⟩
    · exact ⟨_, cover1482⟩
    · exact ⟨_, cover1483⟩
    · exact ⟨_, cover1484⟩
    · exact ⟨_, cover1485⟩
    · exact ⟨_, cover1486⟩
    · exact ⟨_, cover1487⟩
    · exact ⟨_, cover1488⟩

def price : EarlyPrice := ⟨5, 25, 10, 80/100, 70/100, ![6593171948673, 1105695054692, 29878231610, 4780536460], 2762974027178153⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![12588/191, 87397/82, 1275905/246, 4636025/246] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases11
end Z6969Source1639

-- Source: Research6969.PrefixNearSavedHigherHelperCases11
section Z6969Source1640
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases11
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4548,65,1065,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases11.plan Lower6960.Prefix6969RescueData.HigherHelperCases11.plan Lower6960.Prefix6969RescueData.HigherHelperCases11.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 5 16 25 643409 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases11.plan, Lower6960.Prefix6969MainCases.HigherHelperCases11.price, Lower6960.Prefix6969MainCases.HigherHelperCases11.valid, Lower6960.Prefix6969MainCases.HigherHelperCases11.priced, Lower6960.Prefix6969MainCases.HigherHelperCases11.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases11.plan, Lower6960.Prefix6969RescueData.HigherHelperCases11.price, Lower6960.Prefix6969RescueData.HigherHelperCases11.sources, Lower6960.Prefix6969RescueData.HigherHelperCases11.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 213140515692729365 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases11
end Z6969Source1640

-- Source: Research6969.PrefixMainDataHigherHelperCases7
section Z6969Source1641
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases7
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 8, 12, 18, 21, 21, 40, 65, 65, 75] i
  bank i := ![bank3 1490, bank10 1603, bank24 1838, bank37 2039, bank50 2450, bank63 2899, bank89 3732, bank123 3616, bank83 5597, bank147 6388, bank198 9780, bank158 51722, bank171 201573] i
  head := src1678
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15640, 168500, 779261, 3667859],
    ![24861/2, 261931/2, 1194773/2, 5596073/2],
    ![29433/8, 306343/8, 2773444/9, 12832916/9],
    ![17323/9, 175678/9, 1579511/8, 7118149/8],
    ![81680/81, 835420/81, 104516, 4276475/9],
    ![81680/81, 835420/81, 104516, 4276475/9],
    ![250508/361, 2553568/361, 884724/13, 52113648/169],
    ![250508/361, 747976/121, 60568, 50493824/225],
    ![254619/484, 747976/121, 60568, 50493824/225],
    ![254619/484, 561243/100, 2524554/49, 50493824/225],
    ![658228/1323, 957784/189, 30167476/675, 9104528/45],
    ![480716/1323, 957784/189, 30167476/675, 9104528/45],
    ![1826342/5329, 957784/189, 30167476/675, 9104528/45]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 5 1 643409 := by
  refine ⟨?_, rank154 6982, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1678⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free24_0
    · exact free37_0
    · exact free50_0
    · exact free63_0
    · exact free89_0
    · exact free123_0
    · exact free83_1
    · exact free147_0
    · exact free198_0
    · exact free158_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [343109850, 342336983, 342095259, 341651499, 148981215, 148821790, 148605402, 94646905, 70763729, 94862259, 94574267, 147781331, 238786780], [1006145, 1008263, 1008926, 1010142, 2583817, 2586467, 2590065, 4181001, 5665411, 4171491, 4184664, 2603766, 1540391],
  ![126752798559600, 1601846136140, 214908102000, 4268357280], 190204956513957463⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 957784/189, 30167476/675, 9104528/45] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases7
end Z6969Source1641

-- Source: Research6969.PrefixRescueDataHigherHelperCases7
section Z6969Source1642
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases7
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,5,1,1⟩
  bank i := ![bank134 12355, bank141 13899, bank141 15636, bank155 17590, bank193 22261, bank221 28173, bank233 40111, bank232 57109, bank249 57109, bank364 234698] i
  reserve i := ![0, 1, 2, 4, 8, 13, 25, 32, 40, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643409
  seedFloor := 1

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank134 12355
    · exact rank141 13899
    · exact rank141 15636
    · exact rank155 17590
    · exact rank193 22261
    · exact rank221 28173
    · exact rank233 40111
    · exact rank232 57109
    · exact rank249 57109
    · exact rank364 234698
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1427⟩
    · exact ⟨_, cover1428⟩
    · exact ⟨_, cover1429⟩
    · exact ⟨_, cover1430⟩
    · exact ⟨_, cover1431⟩
    · exact ⟨_, cover1432⟩
    · exact ⟨_, cover1433⟩
    · exact ⟨_, cover1434⟩
    · exact ⟨_, cover1435⟩
    · exact ⟨_, cover1438⟩

def price : EarlyPrice := ⟨5, 1, 9, 95/100, 80/100, ![91367227306, 369000989707, 972463906, 3889830644], 1197369580600579⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![21569/191, 237196/191, 1185067/191, 234698/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases7
end Z6969Source1642

-- Source: Research6969.PrefixNearSavedHigherHelperCases7
section Z6969Source1643
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases7
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,5067,112,1241,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases7.plan Lower6960.Prefix6969RescueData.HigherHelperCases7.plan Lower6960.Prefix6969RescueData.HigherHelperCases7.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 5 1 1 643409 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases7.plan, Lower6960.Prefix6969MainCases.HigherHelperCases7.price, Lower6960.Prefix6969MainCases.HigherHelperCases7.valid, Lower6960.Prefix6969MainCases.HigherHelperCases7.priced, Lower6960.Prefix6969MainCases.HigherHelperCases7.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases7.plan, Lower6960.Prefix6969RescueData.HigherHelperCases7.price, Lower6960.Prefix6969RescueData.HigherHelperCases7.sources, Lower6960.Prefix6969RescueData.HigherHelperCases7.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 192455736702780203 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases7
end Z6969Source1643

end Merged_Z6969Pack0714

-- merged module Z6969Pack0715
section Merged_Z6969Pack0715

-- Source: Research6969.PrefixMainDataHigherHelperCases8
section Z6969Source1644
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases8
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 7, 10, 15, 15, 21, 30, 65, 65, 75] i
  bank i := ![bank3 1490, bank10 1603, bank24 1838, bank36 2062, bank42 2497, bank52 2900, bank65 3612, bank93 2947, bank83 5597, bank139 4862, bank198 9780, bank158 51722, bank171 201573] i
  head := src1679
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15193, 168376, 779423, 3736434],
    ![24861/2, 260671/2, 594499, 2769984],
    ![29433/8, 152419/4, 2759864/9, 1411584],
    ![34345/18, 174035/9, 395111/2, 890784],
    ![36739/32, 398869/32, 1203554/9, 17259264/25],
    ![86036/121, 928456/121, 4194896/49, 20044800/49],
    ![86036/121, 928456/121, 4194896/49, 20044800/49],
    ![86036/121, 928456/121, 4194896/49, 40739328/121],
    ![254619/484, 3105668/441, 1091415/16, 40739328/121],
    ![254619/484, 452011/75, 8108024/147, 11202048/49],
    ![658228/1323, 317648/63, 10005472/225, 1001472/5],
    ![480716/1323, 317648/63, 10005472/225, 1001472/5],
    ![1826342/5329, 317648/63, 10005472/225, 1001472/5]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 5 2 643409 := by
  refine ⟨?_, rank154 6912, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1679⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free24_0
    · exact free36_0
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free93_0
    · exact free83_1
    · exact free139_0
    · exact free198_0
    · exact free158_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [338878278, 337487812, 337985126, 338058650, 336708622, 140380645, 138248320, 72503796, 106860691, 99845880, 99340597, 147407103, 238501268], [1017742, 1021553, 1020190, 1019988, 1023688, 2761595, 2808345, 5527115, 3686997, 3961157, 3982482, 2609988, 1542738],
  ![126601243079760, 1602154349272, 214651141200, 4062131640], 188602538519843390⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 317648/63, 10005472/225, 1001472/5] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases8
end Z6969Source1644

-- Source: Research6969.PhysicalChecks101
section Z6969Source1645
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1442 : Request := ⟨⟨⟨560,781,169,15636⟩,5316921262080,10299257375⟩,3,5,1,643409,2⟩
private theorem pass1442_2293 : (Triangular src1442) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1442_2306 : (Triangular src1442) 2306 2346 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1442_2347 : (Triangular src1442) 2347 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1442 : Cover (Triangular src1442) 2389 2293 [2305,2346,2389] := by
  exact ⟨by decide, by decide, pass1442_2293, by decide, by decide, pass1442_2306, by decide, by decide, pass1442_2347, rfl⟩
def src1443 : Request := ⟨⟨⟨560,781,169,17590⟩,5316921262080,10299257375⟩,4,5,1,643409,2⟩
private theorem pass1443_2293 : (Triangular src1443) 2293 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1443_2312 : (Triangular src1443) 2312 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1443_2372 : (Triangular src1443) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1443 : Cover (Triangular src1443) 2389 2293 [2311,2371,2389] := by
  exact ⟨by decide, by decide, pass1443_2293, by decide, by decide, pass1443_2312, by decide, by decide, pass1443_2372, rfl⟩
def src1444 : Request := ⟨⟨⟨690,962,208,22261⟩,9921631092736,23645774460⟩,8,5,1,643409,2⟩
private theorem pass1444_2293 : (Triangular src1444) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1444_2301 : (Triangular src1444) 2301 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1444_2326 : (Triangular src1444) 2326 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1444 : Cover (Triangular src1444) 2389 2293 [2300,2325,2389] := by
  exact ⟨by decide, by decide, pass1444_2293, by decide, by decide, pass1444_2301, by decide, by decide, pass1444_2326, rfl⟩
def src1445 : Request := ⟨⟨⟨1000,1395,307,22261⟩,30557599170560,105715278267⟩,10,5,1,643409,2⟩
private theorem pass1445_2293 : (Triangular src1445) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1445_2294 : (Triangular src1445) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1445_2297 : (Triangular src1445) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1445_2306 : (Triangular src1445) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1445_2332 : (Triangular src1445) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1445 : Cover (Triangular src1445) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass1445_2293, by decide, by decide, pass1445_2294, by decide, by decide, pass1445_2297, by decide, by decide, pass1445_2306, by decide, by decide, pass1445_2332, rfl⟩
def src1446 : Request := ⟨⟨⟨1450,2022,445,40111⟩,92998964346880,465769321795⟩,25,5,1,643409,2⟩
private theorem pass1446_2293 : (Triangular src1446) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1446_2306 : (Triangular src1446) 2306 2342 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1446_2343 : (Triangular src1446) 2343 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1446 : Cover (Triangular src1446) 2389 2293 [2305,2342,2389] := by
  exact ⟨by decide, by decide, pass1446_2293, by decide, by decide, pass1446_2306, by decide, by decide, pass1446_2343, rfl⟩
def src1447 : Request := ⟨⟨⟨2100,2929,645,57109⟩,282396798484480,2049139102608⟩,40,5,1,643409,2⟩
private theorem pass1447_2293 : (Triangular src1447) 2293 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1447_2308 : (Triangular src1447) 2308 2349 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1447_2350 : (Triangular src1447) 2350 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1447 : Cover (Triangular src1447) 2389 2293 [2307,2349,2389] := by
  exact ⟨by decide, by decide, pass1447_2293, by decide, by decide, pass1447_2308, by decide, by decide, pass1447_2350, rfl⟩
def src1449 : Request := ⟨⟨⟨2100,2928,645,146522⟩,282396798484480,2046887686018⟩,65,5,1,643409,2⟩
private theorem pass1449_2293 : (Triangular src1449) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1449_2306 : (Triangular src1449) 2306 2342 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1449_2343 : (Triangular src1449) 2343 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1449 : Cover (Triangular src1449) 2389 2293 [2305,2342,2389] := by
  exact ⟨by decide, by decide, pass1449_2293, by decide, by decide, pass1449_2306, by decide, by decide, pass1449_2343, rfl⟩
def src1451 : Request := ⟨⟨⟨5700,7951,1750,130242⟩,5637370734182400,111025751789870⟩,110,5,1,643409,2⟩
private theorem pass1451_2293 : (Triangular src1451) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1451_2295 : (Triangular src1451) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1451_2300 : (Triangular src1451) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1451_2314 : (Triangular src1451) 2314 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1451_2352 : (Triangular src1451) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1451 : Cover (Triangular src1451) 2389 2293 [2294,2299,2313,2351,2389] := by
  exact ⟨by decide, by decide, pass1451_2293, by decide, by decide, pass1451_2295, by decide, by decide, pass1451_2300, by decide, by decide, pass1451_2314, by decide, by decide, pass1451_2352, rfl⟩
def src1452 : Request := ⟨⟨⟨470,655,144,10983⟩,3184589537280,5168862572⟩,0,5,1,643409,4⟩
private theorem pass1452_2293 : (Triangular src1452) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1452_2303 : (Triangular src1452) 2303 2335 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1452_2336 : (Triangular src1452) 2336 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1452 : Cover (Triangular src1452) 2389 2293 [2302,2335,2389] := by
  exact ⟨by decide, by decide, pass1452_2293, by decide, by decide, pass1452_2303, by decide, by decide, pass1452_2336, rfl⟩
def src1453 : Request := ⟨⟨⟨470,655,144,12355⟩,3184589537280,5168862572⟩,1,5,1,643409,4⟩
private theorem pass1453_2293 : (Triangular src1453) 2293 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1453_2308 : (Triangular src1453) 2308 2356 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1453_2357 : (Triangular src1453) 2357 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1453 : Cover (Triangular src1453) 2389 2293 [2307,2356,2389] := by
  exact ⟨by decide, by decide, pass1453_2293, by decide, by decide, pass1453_2308, by decide, by decide, pass1453_2357, rfl⟩
def src1454 : Request := ⟨⟨⟨470,655,144,13899⟩,3184589537280,5168862572⟩,2,5,1,643409,4⟩
private theorem pass1454_2293 : (Triangular src1454) 2293 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1454_2308 : (Triangular src1454) 2308 2356 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1454_2357 : (Triangular src1454) 2357 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1454 : Cover (Triangular src1454) 2389 2293 [2307,2356,2389] := by
  exact ⟨by decide, by decide, pass1454_2293, by decide, by decide, pass1454_2308, by decide, by decide, pass1454_2357, rfl⟩
def src1455 : Request := ⟨⟨⟨470,655,144,15636⟩,3184589537280,5168862572⟩,3,5,1,643409,4⟩
private theorem pass1455_2293 : (Triangular src1455) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1455_2303 : (Triangular src1455) 2303 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1455_2335 : (Triangular src1455) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1455 : Cover (Triangular src1455) 2389 2293 [2302,2334,2389] := by
  exact ⟨by decide, by decide, pass1455_2293, by decide, by decide, pass1455_2303, by decide, by decide, pass1455_2335, rfl⟩
def src1456 : Request := ⟨⟨⟨470,655,144,17590⟩,3184589537280,5168862572⟩,4,5,1,643409,4⟩
private theorem pass1456_2293 : (Triangular src1456) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1456_2294 : (Triangular src1456) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1456_2297 : (Triangular src1456) 2297 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1456_2307 : (Triangular src1456) 2307 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1456_2339 : (Triangular src1456) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1456 : Cover (Triangular src1456) 2389 2293 [2293,2296,2306,2338,2389] := by
  exact ⟨by decide, by decide, pass1456_2293, by decide, by decide, pass1456_2294, by decide, by decide, pass1456_2297, by decide, by decide, pass1456_2307, by decide, by decide, pass1456_2339, rfl⟩
def src1457 : Request := ⟨⟨⟨690,962,212,19788⟩,10065769922560,23997864317⟩,8,5,1,643409,4⟩
private theorem pass1457_2293 : (Triangular src1457) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1457_2294 : (Triangular src1457) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1457_2297 : (Triangular src1457) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1457_2306 : (Triangular src1457) 2306 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1457_2334 : (Triangular src1457) 2334 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1457 : Cover (Triangular src1457) 2389 2293 [2293,2296,2305,2333,2389] := by
  exact ⟨by decide, by decide, pass1457_2293, by decide, by decide, pass1457_2294, by decide, by decide, pass1457_2297, by decide, by decide, pass1457_2306, by decide, by decide, pass1457_2334, rfl⟩
def src1458 : Request := ⟨⟨⟨1200,1674,368,28173⟩,52718727069696,218807905514⟩,16,5,1,643409,4⟩
private theorem pass1458_2293 : (Triangular src1458) 2293 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1458_2308 : (Triangular src1458) 2308 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1458_2352 : (Triangular src1458) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1458 : Cover (Triangular src1458) 2389 2293 [2307,2351,2389] := by
  exact ⟨by decide, by decide, pass1458_2293, by decide, by decide, pass1458_2308, by decide, by decide, pass1458_2352, rfl⟩
def src1459 : Request := ⟨⟨⟨1750,2441,537,45124⟩,163381988556800,988269431527⟩,32,5,1,643409,4⟩
private theorem pass1459_2293 : (Triangular src1459) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1459_2303 : (Triangular src1459) 2303 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1459_2332 : (Triangular src1459) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1459 : Cover (Triangular src1459) 2389 2293 [2302,2331,2389] := by
  exact ⟨by decide, by decide, pass1459_2293, by decide, by decide, pass1459_2303, by decide, by decide, pass1459_2332, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1645

-- Source: Research6969.PrefixRescueDataHigherHelperCases8
section Z6969Source1646
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases8
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,3⟩
  bank i := ![bank133 12355, bank134 13899, bank155 13899, bank155 15636, bank155 17590, bank192 22261, bank222 22261, bank233 40111, bank249 57109, bank247 146522, bank340 130242] i
  reserve i := ![0, 1, 2, 3, 4, 8, 10, 25, 40, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643409
  seedFloor := 2

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank133 12355
    · exact rank134 13899
    · exact rank155 13899
    · exact rank155 15636
    · exact rank155 17590
    · exact rank192 22261
    · exact rank222 22261
    · exact rank233 40111
    · exact rank249 57109
    · exact rank247 146522
    · exact rank340 130242
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1439⟩
    · exact ⟨_, cover1440⟩
    · exact ⟨_, cover1441⟩
    · exact ⟨_, cover1442⟩
    · exact ⟨_, cover1443⟩
    · exact ⟨_, cover1444⟩
    · exact ⟨_, cover1445⟩
    · exact ⟨_, cover1446⟩
    · exact ⟨_, cover1447⟩
    · exact ⟨_, cover1449⟩
    · exact ⟨_, cover1451⟩

def price : EarlyPrice := ⟨5, 3, 10, 95/100, 80/100, ![171120552926, 230827111805, 2043795250, 2725061500], 1073380136070935⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![918/11, 45164/37, 225021/37, 130242/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases8
end Z6969Source1646

-- Source: Research6969.PrefixNearSavedHigherHelperCases8
section Z6969Source1647
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases8
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,5042,83,1220,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases8.plan Lower6960.Prefix6969RescueData.HigherHelperCases8.plan Lower6960.Prefix6969RescueData.HigherHelperCases8.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 5 2 3 643409 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases8.plan, Lower6960.Prefix6969MainCases.HigherHelperCases8.price, Lower6960.Prefix6969MainCases.HigherHelperCases8.valid, Lower6960.Prefix6969MainCases.HigherHelperCases8.priced, Lower6960.Prefix6969MainCases.HigherHelperCases8.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases8.plan, Lower6960.Prefix6969RescueData.HigherHelperCases8.price, Lower6960.Prefix6969RescueData.HigherHelperCases8.sources, Lower6960.Prefix6969RescueData.HigherHelperCases8.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 193930702664444114 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases8
end Z6969Source1647

-- Source: Research6969.PrefixMainDataHigherHelperCases9
section Z6969Source1648
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases9
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 8, 12, 18, 21, 21, 40, 65, 75, 75] i
  bank i := ![bank3 1490, bank10 1603, bank24 1838, bank37 2039, bank50 2450, bank63 2899, bank89 3732, bank123 3616, bank83 5597, bank147 6388, bank158 51722, bank211 10626, bank171 201573] i
  head := src1680
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15640, 167879, 775742, 3635774],
    ![24861/2, 258205/2, 2355391/4, 10860325/4],
    ![29433/8, 603785/16, 2733286/9, 12452450/9],
    ![17323/9, 692155/36, 3112033/16, 13814225/16],
    ![81680/81, 823000/81, 102975, 8299375/18],
    ![81680/81, 823000/81, 102975, 8299375/18],
    ![250508/361, 2515480/361, 11331258/169, 50568600/169],
    ![250508/361, 735556/121, 60568, 1959872/9],
    ![254619/484, 735556/121, 60568, 1959872/9],
    ![254619/484, 221061/40, 2486259/49, 1959872/9],
    ![480716/1323, 221061/40, 2486259/49, 1959872/9],
    ![480716/1323, 26113640/5329, 117510379/2704, 251969025/1352],
    ![1826342/5329, 26113640/5329, 117510379/2704, 251969025/1352]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 5 4 643409 := by
  refine ⟨?_, rank154 6775, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1680⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free24_0
    · exact free37_0
    · exact free50_0
    · exact free63_0
    · exact free89_0
    · exact free123_0
    · exact free83_1
    · exact free147_0
    · exact free158_0
    · exact free211_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [338900298, 338734367, 337918107, 337290004, 148971301, 149070477, 149092363, 40779823, 70080973, 98926100, 103493640, 145606966, 237126079], [1017682, 1018137, 1020374, 1022095, 2583981, 2582332, 2581969, 9974307, 5719674, 3999976, 3807202, 2647009, 1554045],
  ![125871265254780, 1603640210336, 213413471100, 4530570380], 187543014658110394⟩

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

theorem final_cap : plan.history plan.last = ![1826342/5329, 26113640/5329, 117510379/2704, 251969025/1352] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases9
end Z6969Source1648

-- Source: Research6969.PrefixRescueDataHigherHelperCases9
section Z6969Source1649
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases9
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,8⟩
  bank i := ![bank142 10983, bank142 12355, bank142 13899, bank142 15636, bank142 17590, bank193 19788, bank228 28173, bank242 45124, bank309 102908, bank296 264035, bank365 208621] i
  reserve i := ![0, 1, 2, 3, 4, 8, 16, 32, 85, 110, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643409
  seedFloor := 4

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 10983
    · exact rank142 12355
    · exact rank142 13899
    · exact rank142 15636
    · exact rank142 17590
    · exact rank193 19788
    · exact rank228 28173
    · exact rank242 45124
    · exact rank309 102908
    · exact rank296 264035
    · exact rank365 208621
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1452⟩
    · exact ⟨_, cover1453⟩
    · exact ⟨_, cover1454⟩
    · exact ⟨_, cover1455⟩
    · exact ⟨_, cover1456⟩
    · exact ⟨_, cover1457⟩
    · exact ⟨_, cover1458⟩
    · exact ⟨_, cover1459⟩
    · exact ⟨_, cover1462⟩
    · exact ⟨_, cover1463⟩
    · exact ⟨_, cover1464⟩

def price : EarlyPrice := ⟨5, 8, 10, 90/100, 80/100, ![822296346110, 421987417310, 7935353608, 3967689544], 1463477438395005⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8390/111, 229005/191, 1135721/191, 1668968/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases9
end Z6969Source1649

-- Source: Research6969.PrefixNearSavedHigherHelperCases9
section Z6969Source1650
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases9
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4900,75,1198,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases9.plan Lower6960.Prefix6969RescueData.HigherHelperCases9.plan Lower6960.Prefix6969RescueData.HigherHelperCases9.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 5 4 8 643409 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases9.plan, Lower6960.Prefix6969MainCases.HigherHelperCases9.price, Lower6960.Prefix6969MainCases.HigherHelperCases9.valid, Lower6960.Prefix6969MainCases.HigherHelperCases9.priced, Lower6960.Prefix6969MainCases.HigherHelperCases9.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases9.plan, Lower6960.Prefix6969RescueData.HigherHelperCases9.price, Lower6960.Prefix6969RescueData.HigherHelperCases9.sources, Lower6960.Prefix6969RescueData.HigherHelperCases9.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 200786335487297317 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases9
end Z6969Source1650

-- Source: Research6969.PrefixMainDataRepricedHelperCases2
section Z6969Source1651
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.RepricedHelperCases2
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 9, 10, 16, 17, 20, 23, 21, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank39 1983, bank46 2247, bank55 2427, bank53 2871, bank74 3583, bank98 3253, bank91 4262, bank138 3813, bank118 3641, bank168 4492, bank131 21237, bank153 6368, bank216 10294, bank183 54742, bank174 148759, bank169 292467] i
  head := src1684
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  historyValues := [![16116, 156573, 719601, 3080860],
    ![25417/2, 436985/4, 521808, 2411809],
    ![54680/9, 476510/9, 521808, 7961525/4],
    ![29433/8, 513485/16, 2325886/9, 8592650/9],
    ![64334/25, 21879, 204050, 3705625/4],
    ![11819/6, 290105/18, 2620151/16, 9270525/16],
    ![2483/2, 163285/16, 2959534/25, 420189],
    ![45497/50, 145163/20, 361623/4, 3782075/12],
    ![86808/121, 71570/11, 3544112/49, 3782075/12],
    ![86808/121, 71570/11, 3544112/49, 3045550/11],
    ![86808/121, 56695/9, 2288833/36, 10582009/49],
    ![258784/441, 787634/147, 892889/16, 10582009/49],
    ![258784/441, 787634/147, 892889/16, 53477325/256],
    ![258784/441, 110723/22, 753511/14, 17021675/98],
    ![258784/441, 110723/22, 753511/14, 630003/4],
    ![688141/1681, 110723/22, 753511/14, 630003/4],
    ![688141/1681, 7584040/1681, 9793984/225, 630003/4],
    ![688141/1681, 11066405/2738, 99545726/2601, 26491609/196],
    ![954471/2738, 11066405/2738, 99545726/2601, 26491609/196],
    ![462882/1369, 11066405/2738, 99545726/2601, 26491609/196],
    ![459151/1369, 11066405/2738, 99545726/2601, 26491609/196]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 5 41 643409 := by
  refine ⟨?_, rank154 4675, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1684⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free39_0
    · exact free46_0
    · exact free55_0
    · exact free53_0
    · exact free74_1
    · exact free98_0
    · exact free91_0
    · exact free138_0
    · exact free118_0
    · exact free168_0
    · exact free131_0
    · exact free153_0
    · exact free216_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨50/100, 80/100, [291931416, 291289622, 291209183, 291384821, 291559315, 291749292, 291569748, 220000000, 187029729, 187124563, 147276174, 124283109, 90899666, 124541129, 61809081, 57531987, 85073073, 84985283, 114433491, 161463903, 225750638], [1231601, 1234884, 1235296, 1234397, 1233505, 1232533, 1233451, 1694852, 2026912, 2025768, 2612165, 3143775, 4369963, 3136562, 6511370, 7014312, 4680741, 4685954, 3424114, 2376276, 1647571],
  ![119832953663160, 1615928733412, 203175574200, 5576285260], 155913842217399488⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 19 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 11066405/2738, 99545726/2601, 26491609/196] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.RepricedHelperCases2
end Z6969Source1651

-- Source: Research6969.PrefixRescueDataRepricedHelperCases2
section Z6969Source1652
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.RepricedHelperCases2
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,56⟩
  bank i := ![bank79 3807, bank101 3807, bank134 4282, bank142 5419, bank156 6858, bank224 13899, bank247 25043, bank307 57109, bank334 334168, bank336 64247, bank307 57109] i
  reserve i := ![0, 1, 3, 6, 10, 32, 65, 145, 237, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643409
  seedFloor := 41

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank79 3807
    · exact rank101 3807
    · exact rank134 4282
    · exact rank142 5419
    · exact rank156 6858
    · exact rank224 13899
    · exact rank247 25043
    · exact rank307 57109
    · exact rank334 334168
    · exact rank336 64247
    · exact rank307 57109
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1510⟩
    · exact ⟨_, cover1511⟩
    · exact ⟨_, cover1512⟩
    · exact ⟨_, cover1513⟩
    · exact ⟨_, cover1514⟩
    · exact ⟨_, cover1515⟩
    · exact ⟨_, cover1516⟩
    · exact ⟨_, cover1519⟩
    · exact ⟨_, cover1521⟩
    · exact ⟨_, cover1520⟩
    · exact ⟨_, cover1519⟩

def price : EarlyPrice := ⟨5, 56, 10, 60/100, 50/100, ![7284995398864, 653668491674, 38150696500, 2725061500], 1815234569181006⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![14715/238, 162247/191, 766323/191, 3597832/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.RepricedHelperCases2
end Z6969Source1652

-- Source: Research6969.PrefixNearSavedRepricedHelperCases2
section Z6969Source1653
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedRepricedHelperCases2
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4041,61,849,true⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.RepricedHelperCases2.plan Lower6960.Prefix6969RescueData.RepricedHelperCases2.plan Lower6960.Prefix6969RescueData.RepricedHelperCases2.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  exact ⟨by decide, by decide +kernel⟩

def data : NearCase 5 41 56 643409 :=
  ⟨Lower6960.Prefix6969MainCases.RepricedHelperCases2.plan, Lower6960.Prefix6969MainCases.RepricedHelperCases2.price, Lower6960.Prefix6969MainCases.RepricedHelperCases2.valid, Lower6960.Prefix6969MainCases.RepricedHelperCases2.priced, Lower6960.Prefix6969MainCases.RepricedHelperCases2.sources,
   Lower6960.Prefix6969RescueData.RepricedHelperCases2.plan, Lower6960.Prefix6969RescueData.RepricedHelperCases2.price, Lower6960.Prefix6969RescueData.RepricedHelperCases2.sources, Lower6960.Prefix6969RescueData.RepricedHelperCases2.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 217416423238526044 := by
  unfold NearCase.fee
  unfold Exit.extra
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedRepricedHelperCases2
end Z6969Source1653

-- Source: Research6969.PrefixNearSelect5
section Z6969Source1654
set_option autoImplicit true
namespace Lower6960.Prefix6969Early
set_option maxHeartbeats 8000000

theorem nearChoose5 (j : Fin 56) (ok : UniformAllowed 5 (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧ w≤643409 ∧ ∃ c : NearCase 5 l u w, c.uniform := by
  fin_cases j
  · refine ⟨1, 1, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases7.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases7.fee_exact]; decide +kernel
  · refine ⟨2, 3, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases8.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases8.fee_exact]; decide +kernel
  · refine ⟨2, 3, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases8.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases8.fee_exact]; decide +kernel
  · refine ⟨4, 8, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases9.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases9.fee_exact]; decide +kernel
  · refine ⟨4, 8, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases9.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases9.fee_exact]; decide +kernel
  · refine ⟨4, 8, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases9.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases9.fee_exact]; decide +kernel
  · refine ⟨4, 8, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases9.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases9.fee_exact]; decide +kernel
  · refine ⟨4, 8, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases9.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases9.fee_exact]; decide +kernel
  · refine ⟨9, 15, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases10.fee_exact]; decide +kernel
  · refine ⟨9, 15, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases10.fee_exact]; decide +kernel
  · refine ⟨9, 15, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases10.fee_exact]; decide +kernel
  · refine ⟨9, 15, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases10.fee_exact]; decide +kernel
  · refine ⟨9, 15, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases10.fee_exact]; decide +kernel
  · refine ⟨9, 15, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases10.fee_exact]; decide +kernel
  · refine ⟨9, 15, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases10.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases10.fee_exact]; decide +kernel
  · refine ⟨16, 25, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases11.fee_exact]; decide +kernel
  · refine ⟨16, 25, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases11.fee_exact]; decide +kernel
  · refine ⟨16, 25, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases11.fee_exact]; decide +kernel
  · refine ⟨16, 25, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases11.fee_exact]; decide +kernel
  · refine ⟨16, 25, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases11.fee_exact]; decide +kernel
  · refine ⟨16, 25, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases11.fee_exact]; decide +kernel
  · refine ⟨16, 25, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases11.fee_exact]; decide +kernel
  · refine ⟨16, 25, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases11.fee_exact]; decide +kernel
  · refine ⟨16, 25, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases11.fee_exact]; decide +kernel
  · refine ⟨16, 25, 643409, by decide, by decide, by decide, NearSavedHigherHelperCases11.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases11.fee_exact]; decide +kernel
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 643409, by decide, by decide, by decide, NearSavedRepricedHelperCases2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedRepricedHelperCases2.fee_exact]; decide +kernel

end Lower6960.Prefix6969Early
end Z6969Source1654

-- Source: Research6969.PhysicalChecks115
section Z6969Source1655
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1752 : Request := ⟨⟨⟨325,453,98,4282⟩,1045036793856,1174588250⟩,4,7,1,900773,41⟩
private theorem pass1752_2293 : (Triangular src1752) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1752_2296 : (Triangular src1752) 2296 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1752_2307 : (Triangular src1752) 2307 2346 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1752_2347 : (Triangular src1752) 2347 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1752 : Cover (Triangular src1752) 2389 2293 [2295,2306,2346,2389] := by
  exact ⟨by decide, by decide, pass1752_2293, by decide, by decide, pass1752_2296, by decide, by decide, pass1752_2307, by decide, by decide, pass1752_2347, rfl⟩
def src1753 : Request := ⟨⟨⟨400,558,123,5419⟩,1971918995456,2734096379⟩,8,7,1,900773,41⟩
private theorem pass1753_2293 : (Triangular src1753) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1753_2295 : (Triangular src1753) 2295 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1753_2302 : (Triangular src1753) 2302 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1753_2325 : (Triangular src1753) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1753 : Cover (Triangular src1753) 2389 2293 [2294,2301,2324,2389] := by
  exact ⟨by decide, by decide, pass1753_2293, by decide, by decide, pass1753_2295, by decide, by decide, pass1753_2302, by decide, by decide, pass1753_2325, rfl⟩
def src1754 : Request := ⟨⟨⟨690,962,212,8679⟩,10065769922560,23997864317⟩,20,7,1,900773,41⟩
private theorem pass1754_2293 : (Triangular src1754) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1754_2301 : (Triangular src1754) 2301 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1754_2325 : (Triangular src1754) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1754 : Cover (Triangular src1754) 2389 2293 [2300,2324,2389] := by
  exact ⟨by decide, by decide, pass1754_2293, by decide, by decide, pass1754_2301, by decide, by decide, pass1754_2325, rfl⟩
def src1755 : Request := ⟨⟨⟨1200,1673,378,19788⟩,53798525730816,222977190790⟩,50,7,1,900773,41⟩
private theorem pass1755_2293 : (Triangular src1755) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1755_2297 : (Triangular src1755) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1755_2309 : (Triangular src1755) 2309 2343 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1755_2344 : (Triangular src1755) 2344 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1755 : Cover (Triangular src1755) 2389 2293 [2296,2308,2343,2389] := by
  exact ⟨by decide, by decide, pass1755_2293, by decide, by decide, pass1755_2297, by decide, by decide, pass1755_2309, by decide, by decide, pass1755_2344, rfl⟩
def src1756 : Request := ⟨⟨⟨3200,4461,982,50764⟩,997767489781760,11012145571636⟩,145,7,1,900773,41⟩
private theorem pass1756_2293 : (Triangular src1756) 2293 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1756_2307 : (Triangular src1756) 2307 2345 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1756_2346 : (Triangular src1756) 2346 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1756 : Cover (Triangular src1756) 2389 2293 [2306,2345,2389] := by
  exact ⟨by decide, by decide, pass1756_2293, by decide, by decide, pass1756_2307, by decide, by decide, pass1756_2346, rfl⟩
def src1757 : Request := ⟨⟨⟨3200,4459,1008,264035⟩,1017717693874176,11221829825062⟩,190,7,1,900773,41⟩
private theorem pass1757_2293 : (Triangular src1757) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1757_2298 : (Triangular src1757) 2298 2310 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1757_2311 : (Triangular src1757) 2311 2347 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1757_2348 : (Triangular src1757) 2348 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1757 : Cover (Triangular src1757) 2389 2293 [2297,2310,2347,2389] := by
  exact ⟨by decide, by decide, pass1757_2293, by decide, by decide, pass1757_2298, by decide, by decide, pass1757_2311, by decide, by decide, pass1757_2348, rfl⟩
def src1758 : Request := ⟨⟨⟨3950,5504,1244,1085143⟩,1913299978158080,26038250013848⟩,245,7,1,900773,41⟩
private theorem pass1758_2293 : (Triangular src1758) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1758_2294 : (Triangular src1758) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1758_2297 : (Triangular src1758) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1758_2306 : (Triangular src1758) 2306 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1758_2330 : (Triangular src1758) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1758 : Cover (Triangular src1758) 2389 2293 [2293,2296,2305,2329,2389] := by
  exact ⟨by decide, by decide, pass1758_2293, by decide, by decide, pass1758_2294, by decide, by decide, pass1758_2297, by decide, by decide, pass1758_2306, by decide, by decide, pass1758_2330, rfl⟩
def src1759 : Request := ⟨⟨⟨5700,7946,1796,72277⟩,5749327563587584,113058766636997⟩,245,7,1,900773,41⟩
private theorem pass1759_2293 : (Triangular src1759) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1759_2303 : (Triangular src1759) 2303 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1759_2330 : (Triangular src1759) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1759 : Cover (Triangular src1759) 2389 2293 [2302,2329,2389] := by
  exact ⟨by decide, by decide, pass1759_2293, by decide, by decide, pass1759_2303, by decide, by decide, pass1759_2330, rfl⟩
def src1760 : Request := ⟨⟨⟨556,772,170,6510⟩,5255817068544,9968090926⟩,10,7,2,900772,2⟩
private theorem pass1760_2293 : (Triangular src1760) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1760_2294 : (Triangular src1760) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1760_2297 : (Triangular src1760) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1760_2306 : (Triangular src1760) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1760_2335 : (Triangular src1760) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1760 : Cover (Triangular src1760) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1760_2293, by decide, by decide, pass1760_2294, by decide, by decide, pass1760_2297, by decide, by decide, pass1760_2306, by decide, by decide, pass1760_2335, rfl⟩
def src1761 : Request := ⟨⟨⟨556,772,170,6451⟩,5255817068544,9968090926⟩,10,7,2,900772,3⟩
private theorem pass1761_2293 : (Triangular src1761) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1761_2294 : (Triangular src1761) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1761_2297 : (Triangular src1761) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1761_2306 : (Triangular src1761) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1761_2335 : (Triangular src1761) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1761 : Cover (Triangular src1761) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1761_2293, by decide, by decide, pass1761_2294, by decide, by decide, pass1761_2297, by decide, by decide, pass1761_2306, by decide, by decide, pass1761_2335, rfl⟩
def src1762 : Request := ⟨⟨⟨556,772,170,6334⟩,5255817068544,9968090926⟩,10,7,2,900772,5⟩
private theorem pass1762_2293 : (Triangular src1762) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1762_2294 : (Triangular src1762) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1762_2297 : (Triangular src1762) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1762_2306 : (Triangular src1762) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1762_2335 : (Triangular src1762) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1762 : Cover (Triangular src1762) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1762_2293, by decide, by decide, pass1762_2294, by decide, by decide, pass1762_2297, by decide, by decide, pass1762_2306, by decide, by decide, pass1762_2335, rfl⟩
def src1763 : Request := ⟨⟨⟨556,772,170,6050⟩,5255817068544,9968090926⟩,10,7,2,900772,10⟩
private theorem pass1763_2293 : (Triangular src1763) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1763_2294 : (Triangular src1763) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1763_2297 : (Triangular src1763) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1763_2306 : (Triangular src1763) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1763_2335 : (Triangular src1763) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1763 : Cover (Triangular src1763) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1763_2293, by decide, by decide, pass1763_2294, by decide, by decide, pass1763_2297, by decide, by decide, pass1763_2306, by decide, by decide, pass1763_2335, rfl⟩
def src1764 : Request := ⟨⟨⟨556,772,170,5670⟩,5255817068544,9968090926⟩,10,7,2,900772,17⟩
private theorem pass1764_2293 : (Triangular src1764) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1764_2294 : (Triangular src1764) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1764_2297 : (Triangular src1764) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1764_2306 : (Triangular src1764) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1764_2335 : (Triangular src1764) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1764 : Cover (Triangular src1764) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1764_2293, by decide, by decide, pass1764_2294, by decide, by decide, pass1764_2297, by decide, by decide, pass1764_2306, by decide, by decide, pass1764_2335, rfl⟩
def src1765 : Request := ⟨⟨⟨556,772,170,5173⟩,5255817068544,9968090926⟩,10,7,2,900772,27⟩
private theorem pass1765_2293 : (Triangular src1765) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1765_2294 : (Triangular src1765) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1765_2297 : (Triangular src1765) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1765_2306 : (Triangular src1765) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1765_2335 : (Triangular src1765) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1765 : Cover (Triangular src1765) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1765_2293, by decide, by decide, pass1765_2294, by decide, by decide, pass1765_2297, by decide, by decide, pass1765_2306, by decide, by decide, pass1765_2335, rfl⟩
def src1766 : Request := ⟨⟨⟨556,772,170,4554⟩,5255817068544,9968090926⟩,10,7,2,900772,42⟩
private theorem pass1766_2293 : (Triangular src1766) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1766_2294 : (Triangular src1766) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1766_2297 : (Triangular src1766) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1766_2306 : (Triangular src1766) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1766_2335 : (Triangular src1766) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1766 : Cover (Triangular src1766) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1766_2293, by decide, by decide, pass1766_2294, by decide, by decide, pass1766_2297, by decide, by decide, pass1766_2306, by decide, by decide, pass1766_2335, rfl⟩
def src1767 : Request := ⟨⟨⟨556,772,170,6099⟩,5255817068544,9968090926⟩,10,8,2,1029454,2⟩
private theorem pass1767_2293 : (Triangular src1767) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1767_2294 : (Triangular src1767) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1767_2297 : (Triangular src1767) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1767_2306 : (Triangular src1767) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1767_2335 : (Triangular src1767) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1767 : Cover (Triangular src1767) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1767_2293, by decide, by decide, pass1767_2294, by decide, by decide, pass1767_2297, by decide, by decide, pass1767_2306, by decide, by decide, pass1767_2335, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1655

end Merged_Z6969Pack0715

-- merged module Z6969Pack0716
section Merged_Z6969Pack0716

-- Source: Research6969.PrefixMainDataHigherHelperCases12
section Z6969Source1656
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases12
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 8, 12, 18, 21, 21, 40, 65, 75, 75] i
  bank i := ![bank3 1490, bank10 1603, bank24 1838, bank37 2039, bank50 2450, bank63 2899, bank89 3732, bank123 3616, bank83 5597, bank147 6388, bank158 51722, bank211 10626, bank171 201573] i
  head := src1760
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15640, 167084, 771237, 3594699],
    ![24861/2, 253435/2, 1155833/2, 5217765/2],
    ![29433/8, 296195/8, 2681876/9, 3988460/3],
    ![17323/9, 169660/9, 1525939/8, 6636945/8],
    ![81680/81, 807100/81, 909020/9, 1329125/3],
    ![81680/81, 807100/81, 909020/9, 1329125/3],
    ![250508/361, 2466720/361, 11113428/169, 48590640/169],
    ![250508/361, 719656/121, 60568, 3138688/15],
    ![254619/484, 719656/121, 60568, 3138688/15],
    ![254619/484, 108331/20, 2437234/49, 3138688/15],
    ![480716/1323, 108331/20, 2437234/49, 3138688/15],
    ![480716/1323, 25586820/5329, 26926284/625, 112911876/625],
    ![1826342/5329, 25586820/5329, 26926284/625, 112911876/625]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 6 1 772091 := by
  refine ⟨?_, rank154 6510, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1760⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free24_0
    · exact free37_0
    · exact free50_0
    · exact free63_0
    · exact free89_0
    · exact free123_0
    · exact free83_1
    · exact free147_0
    · exact free158_0
    · exact free211_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [333511258, 333448103, 332721037, 331689630, 148946676, 148798054, 148733031, 36788937, 69206913, 97508350, 104018099, 144743022, 236463093], [1032451, 1032624, 1034617, 1037443, 2584391, 2586862, 2587943, 11078982, 5796412, 4059813, 3785676, 2665950, 1559496],
  ![125519339026260, 1604356464132, 212816783700, 4504954440], 184252465779445460⟩

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
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 25586820/5329, 26926284/625, 112911876/625] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases12
end Z6969Source1656

-- Source: Research6969.PhysicalChecks106
section Z6969Source1657
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1564 : Request := ⟨⟨⟨1200,1673,368,25043⟩,52718727069696,218387554859⟩,25,6,1,772091,1⟩
private theorem pass1564_2293 : (Triangular src1564) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1564_2294 : (Triangular src1564) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1564_2297 : (Triangular src1564) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1564_2305 : (Triangular src1564) 2305 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1564_2329 : (Triangular src1564) 2329 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1564 : Cover (Triangular src1564) 2389 2293 [2293,2296,2304,2328,2389] := by
  exact ⟨by decide, by decide, pass1564_2293, by decide, by decide, pass1564_2294, by decide, by decide, pass1564_2297, by decide, by decide, pass1564_2305, by decide, by decide, pass1564_2329, rfl⟩
def src1565 : Request := ⟨⟨⟨1750,2441,537,35655⟩,163381988556800,988269431527⟩,40,6,1,772091,1⟩
private theorem pass1565_2293 : (Triangular src1565) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1565_2295 : (Triangular src1565) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1565_2301 : (Triangular src1565) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1565_2318 : (Triangular src1565) 2318 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1565_2366 : (Triangular src1565) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1565 : Cover (Triangular src1565) 2389 2293 [2294,2300,2317,2365,2389] := by
  exact ⟨by decide, by decide, pass1565_2293, by decide, by decide, pass1565_2295, by decide, by decide, pass1565_2301, by decide, by decide, pass1565_2318, by decide, by decide, pass1565_2366, rfl⟩
def src1568 : Request := ⟨⟨⟨4800,6694,1474,115771⟩,3367547627110400,55810706074581⟩,145,6,1,772091,1⟩
private theorem pass1568_2293 : (Triangular src1568) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1568_2306 : (Triangular src1568) 2306 2341 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1568_2342 : (Triangular src1568) 2342 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1568 : Cover (Triangular src1568) 2389 2293 [2305,2341,2389] := by
  exact ⟨by decide, by decide, pass1568_2293, by decide, by decide, pass1568_2306, by decide, by decide, pass1568_2342, rfl⟩
def src1569 : Request := ⟨⟨⟨8300,11575,2548,185441⟩,17399709518790656,498569901356632⟩,245,6,1,772091,1⟩
private theorem pass1569_2293 : (Triangular src1569) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1569_2302 : (Triangular src1569) 2302 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1569_2327 : (Triangular src1569) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1569 : Cover (Triangular src1569) 2389 2293 [2301,2326,2389] := by
  exact ⟨by decide, by decide, pass1569_2293, by decide, by decide, pass1569_2302, by decide, by decide, pass1569_2327, rfl⟩
def src1570 : Request := ⟨⟨⟨325,453,98,7715⟩,1045036793856,1174588250⟩,0,6,1,772091,2⟩
private theorem pass1570_2293 : (Triangular src1570) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1570_2298 : (Triangular src1570) 2298 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1570_2316 : (Triangular src1570) 2316 2379 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1570_2380 : (Triangular src1570) 2380 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1570 : Cover (Triangular src1570) 2389 2293 [2297,2315,2379,2389] := by
  exact ⟨by decide, by decide, pass1570_2293, by decide, by decide, pass1570_2298, by decide, by decide, pass1570_2316, by decide, by decide, pass1570_2380, rfl⟩
def src1571 : Request := ⟨⟨⟨325,453,100,8679⟩,1061047500800,1193036697⟩,1,6,1,772091,2⟩
private theorem pass1571_2293 : (Triangular src1571) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1571_2303 : (Triangular src1571) 2303 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1571_2338 : (Triangular src1571) 2338 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1571 : Cover (Triangular src1571) 2389 2293 [2302,2337,2389] := by
  exact ⟨by decide, by decide, pass1571_2293, by decide, by decide, pass1571_2303, by decide, by decide, pass1571_2338, rfl⟩
def src1572 : Request := ⟨⟨⟨400,558,123,9763⟩,1971918995456,2734096379⟩,3,6,1,772091,2⟩
private theorem pass1572_2293 : (Triangular src1572) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1572_2296 : (Triangular src1572) 2296 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1572_2306 : (Triangular src1572) 2306 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1572_2339 : (Triangular src1572) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1572 : Cover (Triangular src1572) 2389 2293 [2295,2305,2338,2389] := by
  exact ⟨by decide, by decide, pass1572_2293, by decide, by decide, pass1572_2296, by decide, by decide, pass1572_2306, by decide, by decide, pass1572_2339, rfl⟩
def src1573 : Request := ⟨⟨⟨470,655,144,12355⟩,3184589537280,5168862572⟩,6,6,1,772091,2⟩
private theorem pass1573_2293 : (Triangular src1573) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1573_2299 : (Triangular src1573) 2299 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1573_2318 : (Triangular src1573) 2318 2379 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1573_2380 : (Triangular src1573) 2380 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1573 : Cover (Triangular src1573) 2389 2293 [2298,2317,2379,2389] := by
  exact ⟨by decide, by decide, pass1573_2293, by decide, by decide, pass1573_2299, by decide, by decide, pass1573_2318, by decide, by decide, pass1573_2380, rfl⟩
def src1574 : Request := ⟨⟨⟨560,781,176,15636⟩,5482316038144,10627925923⟩,10,6,1,772091,2⟩
private theorem pass1574_2293 : (Triangular src1574) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1574_2295 : (Triangular src1574) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1574_2301 : (Triangular src1574) 2301 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1574_2320 : (Triangular src1574) 2320 2379 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1574_2380 : (Triangular src1574) 2380 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1574 : Cover (Triangular src1574) 2389 2293 [2294,2300,2319,2379,2389] := by
  exact ⟨by decide, by decide, pass1574_2293, by decide, by decide, pass1574_2295, by decide, by decide, pass1574_2301, by decide, by decide, pass1574_2320, by decide, by decide, pass1574_2380, rfl⟩
def src1575 : Request := ⟨⟨⟨825,1150,248,19788⟩,16903818182656,48121815022⟩,16,6,1,772091,2⟩
private theorem pass1575_2293 : (Triangular src1575) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1575_2297 : (Triangular src1575) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1575_2309 : (Triangular src1575) 2309 2345 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1575_2346 : (Triangular src1575) 2346 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1575 : Cover (Triangular src1575) 2389 2293 [2296,2308,2345,2389] := by
  exact ⟨by decide, by decide, pass1575_2293, by decide, by decide, pass1575_2297, by decide, by decide, pass1575_2309, by decide, by decide, pass1575_2346, rfl⟩
def src1576 : Request := ⟨⟨⟨1200,1673,368,25043⟩,52718727069696,218387554859⟩,25,6,1,772091,2⟩
private theorem pass1576_2293 : (Triangular src1576) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1576_2303 : (Triangular src1576) 2303 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1576_2332 : (Triangular src1576) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1576 : Cover (Triangular src1576) 2389 2293 [2302,2331,2389] := by
  exact ⟨by decide, by decide, pass1576_2293, by decide, by decide, pass1576_2303, by decide, by decide, pass1576_2332, rfl⟩
def src1577 : Request := ⟨⟨⟨1200,1673,368,130242⟩,52718727069696,218387554859⟩,50,6,1,772091,2⟩
private theorem pass1577_2293 : (Triangular src1577) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1577_2299 : (Triangular src1577) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1577_2316 : (Triangular src1577) 2316 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1577_2365 : (Triangular src1577) 2365 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1577 : Cover (Triangular src1577) 2389 2293 [2298,2315,2364,2389] := by
  exact ⟨by decide, by decide, pass1577_2293, by decide, by decide, pass1577_2299, by decide, by decide, pass1577_2316, by decide, by decide, pass1577_2365, rfl⟩
def src1579 : Request := ⟨⟨⟨2100,2928,645,57109⟩,282396798484480,2046887686018⟩,65,6,1,772091,2⟩
private theorem pass1579_2293 : (Triangular src1579) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1579_2296 : (Triangular src1579) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1579_2304 : (Triangular src1579) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1579_2327 : (Triangular src1579) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1579 : Cover (Triangular src1579) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass1579_2293, by decide, by decide, pass1579_2296, by decide, by decide, pass1579_2304, by decide, by decide, pass1579_2327, rfl⟩
def src1581 : Request := ⟨⟨⟨4800,6694,1445,115771⟩,3317023033262080,54952917346103⟩,145,6,1,772091,2⟩
private theorem pass1581_2293 : (Triangular src1581) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1581_2294 : (Triangular src1581) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1581_2297 : (Triangular src1581) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1581_2305 : (Triangular src1581) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1581_2327 : (Triangular src1581) 2327 2388 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1581_2389 : (Triangular src1581) 2389 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1581 : Cover (Triangular src1581) 2389 2293 [2293,2296,2304,2326,2388,2389] := by
  exact ⟨by decide, by decide, pass1581_2293, by decide, by decide, pass1581_2294, by decide, by decide, pass1581_2297, by decide, by decide, pass1581_2305, by decide, by decide, pass1581_2327, by decide, by decide, pass1581_2389, rfl⟩
def src1582 : Request := ⟨⟨⟨8300,11575,2548,185441⟩,17399709518790656,498569901356632⟩,245,6,1,772091,2⟩
private theorem pass1582_2293 : (Triangular src1582) 2293 2309 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1582_2310 : (Triangular src1582) 2310 2356 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1582_2357 : (Triangular src1582) 2357 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1582 : Cover (Triangular src1582) 2389 2293 [2309,2356,2389] := by
  exact ⟨by decide, by decide, pass1582_2293, by decide, by decide, pass1582_2310, by decide, by decide, pass1582_2357, rfl⟩
def src1583 : Request := ⟨⟨⟨325,453,98,7715⟩,1045036793856,1174588250⟩,0,6,1,772091,4⟩
private theorem pass1583_2293 : (Triangular src1583) 2293 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1583_2317 : (Triangular src1583) 2317 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1583 : Cover (Triangular src1583) 2389 2293 [2316,2389] := by
  exact ⟨by decide, by decide, pass1583_2293, by decide, by decide, pass1583_2317, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1657

-- Source: Research6969.PrefixRescueDataHigherHelperCases12
section Z6969Source1658
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases12
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,1⟩
  bank i := ![bank101 7715, bank101 8679, bank133 9763, bank141 10983, bank156 13899, bank193 17590, bank222 22261, bank224 25043, bank242 35655, bank322 115771, bank362 185441] i
  reserve i := ![0, 1, 2, 4, 8, 13, 20, 25, 40, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 772091
  seedFloor := 1

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 7715
    · exact rank101 8679
    · exact rank133 9763
    · exact rank141 10983
    · exact rank156 13899
    · exact rank193 17590
    · exact rank222 22261
    · exact rank224 25043
    · exact rank242 35655
    · exact rank322 115771
    · exact rank362 185441
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1557⟩
    · exact ⟨_, cover1558⟩
    · exact ⟨_, cover1559⟩
    · exact ⟨_, cover1560⟩
    · exact ⟨_, cover1561⟩
    · exact ⟨_, cover1562⟩
    · exact ⟨_, cover1563⟩
    · exact ⟨_, cover1564⟩
    · exact ⟨_, cover1565⟩
    · exact ⟨_, cover1568⟩
    · exact ⟨_, cover1569⟩

def price : EarlyPrice := ⟨6, 1, 10, 95/100, 80/100, ![72191624977, 364469712730, 991928756, 4959608108], 676811162517222⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![7032/73, 62663/82, 1124221/246, 185441/246] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases12
end Z6969Source1658

-- Source: Research6969.PrefixNearSavedHigherHelperCases12
section Z6969Source1659
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases12
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4801,96,764,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases12.plan Lower6960.Prefix6969RescueData.HigherHelperCases12.plan Lower6960.Prefix6969RescueData.HigherHelperCases12.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 6 1 1 772091 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases12.plan, Lower6960.Prefix6969MainCases.HigherHelperCases12.price, Lower6960.Prefix6969MainCases.HigherHelperCases12.valid, Lower6960.Prefix6969MainCases.HigherHelperCases12.priced, Lower6960.Prefix6969MainCases.HigherHelperCases12.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases12.plan, Lower6960.Prefix6969RescueData.HigherHelperCases12.price, Lower6960.Prefix6969RescueData.HigherHelperCases12.sources, Lower6960.Prefix6969RescueData.HigherHelperCases12.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 185816290822558570 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases12
end Z6969Source1659

-- Source: Research6969.PrefixMainDataHigherHelperCases13
section Z6969Source1660
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases13
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 7, 10, 15, 15, 21, 30, 65, 65, 75] i
  bank i := ![bank3 1490, bank10 1603, bank24 1838, bank36 2062, bank42 2497, bank52 2900, bank65 3612, bank93 2947, bank83 5597, bank139 4862, bank199 9241, bank158 51722, bank171 201573] i
  head := src1761
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15193, 166993, 771586, 3664518],
    ![24861/2, 252373/2, 2301931/4, 10340953/4],
    ![29433/8, 589853/16, 2670430/9, 11856938/9],
    ![34345/18, 336545/18, 3056241/16, 6650981/8],
    ![36739/32, 193211/16, 1203554/9, 16108147/25],
    ![86036/121, 899413/121, 4064433/49, 18707900/49],
    ![86036/121, 899413/121, 4064433/49, 18707900/49],
    ![86036/121, 899413/121, 4064433/49, 38022194/121],
    ![254619/484, 3025454/441, 1091415/16, 38022194/121],
    ![254619/484, 871291/150, 7817594/147, 31364762/147],
    ![694280/1323, 918850/189, 10525499/242, 119227382/675],
    ![480716/1323, 918850/189, 10525499/242, 119227382/675],
    ![1826342/5329, 918850/189, 10525499/242, 119227382/675]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 6 2 772091 := by
  refine ⟨?_, rank154 6451, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1761⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free24_0
    · exact free36_0
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free93_0
    · exact free83_1
    · exact free139_0
    · exact free199_0
    · exact free158_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [329709449, 329157230, 329090072, 328302980, 329492083, 115460038, 113571836, 58791969, 86878009, 95587373, 94443752, 145486723, 237031392], [1042870, 1044384, 1044568, 1046725, 1043466, 3390416, 3454025, 6858031, 4573565, 4140888, 4191245, 2649645, 1554823],
  ![125821003501440, 1603742236188, 213328252800, 4275069900], 182939944658958348⟩

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
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
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

theorem final_cap : plan.history plan.last = ![1826342/5329, 918850/189, 10525499/242, 119227382/675] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases13
end Z6969Source1660

-- Source: Research6969.PrefixRescueDataHigherHelperCases13
section Z6969Source1661
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases13
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,3⟩
  bank i := ![bank100 7715, bank101 8679, bank134 9763, bank142 12355, bank157 15636, bank200 19788, bank224 25043, bank247 57109, bank224 130242, bank321 115771, bank362 185441] i
  reserve i := ![0, 1, 3, 6, 10, 16, 25, 65, 50, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 772091
  seedFloor := 2

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank100 7715
    · exact rank101 8679
    · exact rank134 9763
    · exact rank142 12355
    · exact rank157 15636
    · exact rank200 19788
    · exact rank224 25043
    · exact rank247 57109
    · exact rank224 130242
    · exact rank321 115771
    · exact rank362 185441
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1570⟩
    · exact ⟨_, cover1571⟩
    · exact ⟨_, cover1572⟩
    · exact ⟨_, cover1573⟩
    · exact ⟨_, cover1574⟩
    · exact ⟨_, cover1575⟩
    · exact ⟨_, cover1576⟩
    · exact ⟨_, cover1579⟩
    · exact ⟨_, cover1577⟩
    · exact ⟨_, cover1581⟩
    · exact ⟨_, cover1582⟩

def price : EarlyPrice := ⟨6, 3, 10, 95/100, 80/100, ![216573391403, 371498008552, 2975765884, 4959608108], 750537346623427⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![1171/17, 193085/246, 382457/82, 185441/82] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases13
end Z6969Source1661

-- Source: Research6969.PrefixNearSavedHigherHelperCases13
section Z6969Source1662
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases13
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4861,68,784,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases13.plan Lower6960.Prefix6969RescueData.HigherHelperCases13.plan Lower6960.Prefix6969RescueData.HigherHelperCases13.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 6 2 3 772091 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases13.plan, Lower6960.Prefix6969MainCases.HigherHelperCases13.price, Lower6960.Prefix6969MainCases.HigherHelperCases13.valid, Lower6960.Prefix6969MainCases.HigherHelperCases13.priced, Lower6960.Prefix6969MainCases.HigherHelperCases13.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases13.plan, Lower6960.Prefix6969RescueData.HigherHelperCases13.price, Lower6960.Prefix6969RescueData.HigherHelperCases13.sources, Lower6960.Prefix6969RescueData.HigherHelperCases13.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 187041705836896679 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases13
end Z6969Source1662

-- Source: Research6969.PrefixMainDataHigherHelperCases14
section Z6969Source1663
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases14
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 11
  reserve i := ![0, 1, 2, 3, 5, 8, 12, 21, 21, 65, 65, 75] i
  bank i := ![bank3 1490, bank10 1603, bank19 1656, bank24 1838, bank37 2039, bank50 2450, bank63 2899, bank108 3859, bank83 5597, bank167 24691, bank199 9241, bank171 201573] i
  head := src1762
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8]
  historyValues := [![15589, 166061, 766836, 3562933],
    ![24861/2, 250267/2, 1141313/2, 2569609],
    ![6218, 541214/9, 1141313/2, 2569609],
    ![29433/8, 292411/8, 2647732/9, 11641892/9],
    ![17323/9, 167416/9, 1505963/8, 6457513/8],
    ![81680/81, 796540/81, 99692, 3879575/9],
    ![81680/81, 796540/81, 99692, 3879575/9],
    ![76938/121, 704782/121, 1863897/32, 14891881/64],
    ![254619/484, 704782/121, 1863897/32, 14891881/64],
    ![55840/147, 704782/121, 1863897/32, 14891881/64],
    ![55840/147, 6372280/1323, 10525499/242, 85396081/484],
    ![1826342/5329, 6372280/1323, 10525499/242, 85396081/484]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 6 4 772091 := by
  refine ⟨?_, rank154 6334, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1762⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free19_0
    · exact free24_0
    · exact free37_0
    · exact free50_0
    · exact free63_0
    · exact free108_0
    · exact free83_1
    · exact free167_0
    · exact free199_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [329071568, 327494607, 327459844, 328865926, 328125342, 166871313, 166979956, 155436578, 100443186, 100127842, 148624827, 236883277], [1044618, 1049667, 1049845, 1045182, 1047212, 2286371, 2284564, 2476488, 3935947, 3949257, 2589742, 1556041],
  ![125742381097140, 1603902365288, 213194949300, 4028242140], 182470384265829151⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 6372280/1323, 10525499/242, 85396081/484] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases14
end Z6969Source1663

-- Source: Research6969.PhysicalChecks107
section Z6969Source1664
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1584 : Request := ⟨⟨⟨325,453,98,8679⟩,1045036793856,1174588250⟩,1,6,1,772091,4⟩
private theorem pass1584_2293 : (Triangular src1584) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1584_2302 : (Triangular src1584) 2302 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1584_2335 : (Triangular src1584) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1584 : Cover (Triangular src1584) 2389 2293 [2301,2334,2389] := by
  exact ⟨by decide, by decide, pass1584_2293, by decide, by decide, pass1584_2302, by decide, by decide, pass1584_2335, rfl⟩
def src1585 : Request := ⟨⟨⟨325,453,100,9763⟩,1061047500800,1193036697⟩,2,6,1,772091,4⟩
private theorem pass1585_2293 : (Triangular src1585) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1585_2300 : (Triangular src1585) 2300 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1585_2325 : (Triangular src1585) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1585 : Cover (Triangular src1585) 2389 2293 [2299,2324,2389] := by
  exact ⟨by decide, by decide, pass1585_2293, by decide, by decide, pass1585_2300, by decide, by decide, pass1585_2325, rfl⟩
def src1586 : Request := ⟨⟨⟨400,558,123,10983⟩,1971918995456,2734096379⟩,4,6,1,772091,4⟩
private theorem pass1586_2293 : (Triangular src1586) 2293 2309 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1586_2310 : (Triangular src1586) 2310 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1586_2367 : (Triangular src1586) 2367 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1586 : Cover (Triangular src1586) 2389 2293 [2309,2366,2389] := by
  exact ⟨by decide, by decide, pass1586_2293, by decide, by decide, pass1586_2310, by decide, by decide, pass1586_2367, rfl⟩
def src1587 : Request := ⟨⟨⟨470,655,144,12355⟩,3184589537280,5168862572⟩,6,6,1,772091,4⟩
private theorem pass1587_2293 : (Triangular src1587) 2293 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1587_2315 : (Triangular src1587) 2315 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1587_2387 : (Triangular src1587) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1587 : Cover (Triangular src1587) 2389 2293 [2314,2386,2389] := by
  exact ⟨by decide, by decide, pass1587_2293, by decide, by decide, pass1587_2315, by decide, by decide, pass1587_2387, rfl⟩
def src1588 : Request := ⟨⟨⟨690,962,212,13899⟩,10065769922560,23997864317⟩,10,6,1,772091,4⟩
private theorem pass1588_2293 : (Triangular src1588) 2293 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1588_2304 : (Triangular src1588) 2304 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1588_2338 : (Triangular src1588) 2338 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1588 : Cover (Triangular src1588) 2389 2293 [2303,2337,2389] := by
  exact ⟨by decide, by decide, pass1588_2293, by decide, by decide, pass1588_2304, by decide, by decide, pass1588_2338, rfl⟩
def src1589 : Request := ⟨⟨⟨1000,1395,307,17590⟩,30557599170560,105715278267⟩,16,6,1,772091,4⟩
private theorem pass1589_2293 : (Triangular src1589) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1589_2294 : (Triangular src1589) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1589_2297 : (Triangular src1589) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1589_2306 : (Triangular src1589) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1589_2332 : (Triangular src1589) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1589 : Cover (Triangular src1589) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass1589_2293, by decide, by decide, pass1589_2294, by decide, by decide, pass1589_2297, by decide, by decide, pass1589_2306, by decide, by decide, pass1589_2332, rfl⟩
def src1590 : Request := ⟨⟨⟨1450,2022,445,35655⟩,92998964346880,465769321795⟩,40,6,1,772091,4⟩
private theorem pass1590_2293 : (Triangular src1590) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1590_2294 : (Triangular src1590) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1590_2297 : (Triangular src1590) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1590_2305 : (Triangular src1590) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1590_2328 : (Triangular src1590) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1590 : Cover (Triangular src1590) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass1590_2293, by decide, by decide, pass1590_2294, by decide, by decide, pass1590_2297, by decide, by decide, pass1590_2305, by decide, by decide, pass1590_2328, rfl⟩
def src1592 : Request := ⟨⟨⟨1450,2021,445,208621⟩,92998964346880,465028319332⟩,65,6,1,772091,4⟩
private theorem pass1592_2293 : (Triangular src1592) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1592_2294 : (Triangular src1592) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1592_2297 : (Triangular src1592) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1592_2305 : (Triangular src1592) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1592_2328 : (Triangular src1592) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1592 : Cover (Triangular src1592) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass1592_2293, by decide, by decide, pass1592_2294, by decide, by decide, pass1592_2297, by decide, by decide, pass1592_2305, by decide, by decide, pass1592_2328, rfl⟩
def src1593 : Request := ⟨⟨⟨3200,4463,982,64247⟩,997767489781760,11028049925768⟩,85,6,1,772091,4⟩
private theorem pass1593_2293 : (Triangular src1593) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1593_2299 : (Triangular src1593) 2299 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1593_2315 : (Triangular src1593) 2315 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1593_2360 : (Triangular src1593) 2360 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1593 : Cover (Triangular src1593) 2389 2293 [2298,2314,2359,2389] := by
  exact ⟨by decide, by decide, pass1593_2293, by decide, by decide, pass1593_2299, by decide, by decide, pass1593_2315, by decide, by decide, pass1593_2360, rfl⟩
def src1595 : Request := ⟨⟨⟨5700,7950,1750,102908⟩,5637370734182400,110980791054694⟩,145,6,1,772091,4⟩
private theorem pass1595_2293 : (Triangular src1595) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1595_2294 : (Triangular src1595) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1595_2297 : (Triangular src1595) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1595_2305 : (Triangular src1595) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1595_2327 : (Triangular src1595) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1595_2388 : (Triangular src1595) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1595 : Cover (Triangular src1595) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass1595_2293, by decide, by decide, pass1595_2294, by decide, by decide, pass1595_2297, by decide, by decide, pass1595_2305, by decide, by decide, pass1595_2327, by decide, by decide, pass1595_2388, rfl⟩
def src1596 : Request := ⟨⟨⟨325,453,98,6858⟩,1045036793856,1174588250⟩,0,6,1,772091,9⟩
private theorem pass1596_2293 : (Triangular src1596) 2293 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1596_2312 : (Triangular src1596) 2312 2379 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1596_2380 : (Triangular src1596) 2380 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1596 : Cover (Triangular src1596) 2389 2293 [2311,2379,2389] := by
  exact ⟨by decide, by decide, pass1596_2293, by decide, by decide, pass1596_2312, by decide, by decide, pass1596_2380, rfl⟩
def src1597 : Request := ⟨⟨⟨325,453,98,7715⟩,1045036793856,1174588250⟩,1,6,1,772091,9⟩
private theorem pass1597_2293 : (Triangular src1597) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1597_2298 : (Triangular src1597) 2298 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1597_2316 : (Triangular src1597) 2316 2380 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1597_2381 : (Triangular src1597) 2381 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1597 : Cover (Triangular src1597) 2389 2293 [2297,2315,2380,2389] := by
  exact ⟨by decide, by decide, pass1597_2293, by decide, by decide, pass1597_2298, by decide, by decide, pass1597_2316, by decide, by decide, pass1597_2381, rfl⟩
def src1598 : Request := ⟨⟨⟨400,558,123,8679⟩,1971918995456,2734096379⟩,3,6,1,772091,9⟩
private theorem pass1598_2293 : (Triangular src1598) 2293 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1598_2309 : (Triangular src1598) 2309 2362 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1598_2363 : (Triangular src1598) 2363 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1598 : Cover (Triangular src1598) 2389 2293 [2308,2362,2389] := by
  exact ⟨by decide, by decide, pass1598_2293, by decide, by decide, pass1598_2309, by decide, by decide, pass1598_2363, rfl⟩
def src1599 : Request := ⟨⟨⟨470,655,144,10983⟩,3184589537280,5168862572⟩,6,6,1,772091,9⟩
private theorem pass1599_2293 : (Triangular src1599) 2293 2310 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1599_2311 : (Triangular src1599) 2311 2369 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1599_2370 : (Triangular src1599) 2370 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1599 : Cover (Triangular src1599) 2389 2293 [2310,2369,2389] := by
  exact ⟨by decide, by decide, pass1599_2293, by decide, by decide, pass1599_2311, by decide, by decide, pass1599_2370, rfl⟩
def src1600 : Request := ⟨⟨⟨560,781,172,13899⟩,5388141854720,10440670587⟩,10,6,1,772091,9⟩
private theorem pass1600_2293 : (Triangular src1600) 2293 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1600_2304 : (Triangular src1600) 2304 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1600_2339 : (Triangular src1600) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1600 : Cover (Triangular src1600) 2389 2293 [2303,2338,2389] := by
  exact ⟨by decide, by decide, pass1600_2293, by decide, by decide, pass1600_2304, by decide, by decide, pass1600_2339, rfl⟩
def src1601 : Request := ⟨⟨⟨1000,1395,301,19788⟩,30103476895744,104105680031⟩,20,6,1,772091,9⟩
private theorem pass1601_2293 : (Triangular src1601) 2293 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1601_2307 : (Triangular src1601) 2307 2348 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1601_2349 : (Triangular src1601) 2349 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1601 : Cover (Triangular src1601) 2389 2293 [2306,2348,2389] := by
  exact ⟨by decide, by decide, pass1601_2293, by decide, by decide, pass1601_2307, by decide, by decide, pass1601_2349, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1664

-- Source: Research6969.PrefixRescueDataHigherHelperCases14
section Z6969Source1665
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases14
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,8⟩
  bank i := ![bank100 7715, bank100 8679, bank101 9763, bank134 10983, bank142 12355, bank193 13899, bank222 17590, bank233 35655, bank297 64247, bank231 208621, bank338 102908] i
  reserve i := ![0, 1, 2, 4, 6, 10, 16, 40, 85, 65, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 772091
  seedFloor := 4

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank100 7715
    · exact rank100 8679
    · exact rank101 9763
    · exact rank134 10983
    · exact rank142 12355
    · exact rank193 13899
    · exact rank222 17590
    · exact rank233 35655
    · exact rank297 64247
    · exact rank231 208621
    · exact rank338 102908
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1583⟩
    · exact ⟨_, cover1584⟩
    · exact ⟨_, cover1585⟩
    · exact ⟨_, cover1586⟩
    · exact ⟨_, cover1587⟩
    · exact ⟨_, cover1588⟩
    · exact ⟨_, cover1589⟩
    · exact ⟨_, cover1590⟩
    · exact ⟨_, cover1593⟩
    · exact ⟨_, cover1592⟩
    · exact ⟨_, cover1595⟩

def price : EarlyPrice := ⟨6, 8, 10, 90/100, 80/100, ![649717976866, 410982935787, 5450105500, 3406324250], 914242888723615⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![193/3, 58454/73, 340524/73, 411632/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases14
end Z6969Source1665

-- Source: Research6969.PrefixNearSavedHigherHelperCases14
section Z6969Source1666
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases14
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4816,64,800,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases14.plan Lower6960.Prefix6969RescueData.HigherHelperCases14.plan Lower6960.Prefix6969RescueData.HigherHelperCases14.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 6 4 8 772091 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases14.plan, Lower6960.Prefix6969MainCases.HigherHelperCases14.price, Lower6960.Prefix6969MainCases.HigherHelperCases14.valid, Lower6960.Prefix6969MainCases.HigherHelperCases14.priced, Lower6960.Prefix6969MainCases.HigherHelperCases14.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases14.plan, Lower6960.Prefix6969RescueData.HigherHelperCases14.price, Lower6960.Prefix6969RescueData.HigherHelperCases14.sources, Lower6960.Prefix6969RescueData.HigherHelperCases14.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 193334179196643166 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases14
end Z6969Source1666

-- Source: Research6969.PrefixMainDataHigherHelperCases15
section Z6969Source1667
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases15
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 65, 105, 75, 75] i
  bank i := ![bank3 1490, bank10 1603, bank19 1656, bank24 1838, bank28 2005, bank37 2039, bank42 2497, bank52 2900, bank65 3612, bank83 5597, bank83 2752, bank123 3616, bank122 24063, bank159 6076, bank199 9241, bank158 51722, bank230 14067, bank172 88577, bank171 201573] i
  head := src1763
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14995, 163894, 756151, 3637741],
    ![24861/2, 245155/2, 1117883/2, 2569609],
    ![6218, 529570/9, 1117883/2, 2504700],
    ![29433/8, 286305/8, 864212/3, 11119900/9],
    ![62542/25, 24766, 411025/2, 4020025/4],
    ![17323/9, 163795/9, 1473729/8, 6167975/8],
    ![36739/32, 375595/32, 1203554/9, 604274],
    ![86036/121, 874150/121, 3950950/49, 17545000/49],
    ![86036/121, 874150/121, 3950950/49, 17545000/49],
    ![254619/484, 60320/9, 3340192/49, 17545000/49],
    ![254619/484, 60320/9, 3340192/49, 332992],
    ![254619/484, 692056/121, 60568, 204304],
    ![41249/100, 692056/121, 60568, 204304],
    ![41249/100, 209167/40, 48422, 188356],
    ![41249/100, 6227440/1323, 21037503/484, 693075/4],
    ![480716/1323, 6227440/1323, 21037503/484, 693075/4],
    ![480716/1323, 41150/9, 17867645/432, 7880125/48],
    ![1872696/5329, 41150/9, 17867645/432, 7880125/48],
    ![1826342/5329, 41150/9, 17867645/432, 7880125/48]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 6 9 772091 := by
  refine ⟨?_, rank154 6050, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1763⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free19_0
    · exact free24_0
    · exact free28_0
    · exact free37_0
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free83_1
    · exact free83_0
    · exact free123_0
    · exact free122_0
    · exact free159_0
    · exact free199_0
    · exact free158_0
    · exact free230_0
    · exact free172_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [317929608, 317578016, 316838168, 316974592, 316355098, 316779987, 317322018, 146948332, 147088938, 147177836, 146986348, 69950410, 69987922, 83251608, 82671942, 124211412, 100670807, 139322072, 234160786], [1098600, 1100399, 1104184, 1103486, 1106655, 1104481, 1101708, 2617616, 2615278, 2613800, 2616984, 5730051, 5727070, 4788899, 4823320, 3145779, 3926341, 2784803, 1578425],
  ![124297228424520, 1606843579724, 211159400400, 5347824300], 174301657589483538⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 41150/9, 17867645/432, 7880125/48] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases15
end Z6969Source1667

end Merged_Z6969Pack0716

-- merged module Z6969Pack0717
section Merged_Z6969Pack0717

-- Source: Research6969.PhysicalChecks108
section Z6969Source1668
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1602 : Request := ⟨⟨⟨1450,2022,457,31694⟩,94890063298560,475487789910⟩,40,6,1,772091,9⟩
private theorem pass1602_2293 : (Triangular src1602) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1602_2294 : (Triangular src1602) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1602_2297 : (Triangular src1602) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1602_2306 : (Triangular src1602) 2306 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1602_2331 : (Triangular src1602) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1602 : Cover (Triangular src1602) 2389 2293 [2293,2296,2305,2330,2389] := by
  exact ⟨by decide, by decide, pass1602_2293, by decide, by decide, pass1602_2294, by decide, by decide, pass1602_2297, by decide, by decide, pass1602_2306, by decide, by decide, pass1602_2331, rfl⟩
def src1603 : Request := ⟨⟨⟨1200,1673,378,102908⟩,53798525730816,222977190790⟩,50,6,1,772091,9⟩
private theorem pass1603_2293 : (Triangular src1603) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1603_2294 : (Triangular src1603) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1603_2297 : (Triangular src1603) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1603_2306 : (Triangular src1603) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1603_2332 : (Triangular src1603) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1603 : Cover (Triangular src1603) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass1603_2293, by decide, by decide, pass1603_2294, by decide, by decide, pass1603_2297, by decide, by decide, pass1603_2306, by decide, by decide, pass1603_2332, rfl⟩
def src1605 : Request := ⟨⟨⟨3200,4463,982,57109⟩,997767489781760,11028049925768⟩,85,6,1,772091,9⟩
private theorem pass1605_2293 : (Triangular src1605) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1605_2294 : (Triangular src1605) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1605_2296 : (Triangular src1605) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1605_2302 : (Triangular src1605) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1605_2319 : (Triangular src1605) 2319 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1605_2366 : (Triangular src1605) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1605 : Cover (Triangular src1605) 2389 2293 [2293,2295,2301,2318,2365,2389] := by
  exact ⟨by decide, by decide, pass1605_2293, by decide, by decide, pass1605_2294, by decide, by decide, pass1605_2296, by decide, by decide, pass1605_2302, by decide, by decide, pass1605_2319, by decide, by decide, pass1605_2366, rfl⟩
def src1607 : Request := ⟨⟨⟨5700,7950,1796,91474⟩,5749327563587584,113242283843565⟩,145,6,1,772091,9⟩
private theorem pass1607_2293 : (Triangular src1607) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1607_2294 : (Triangular src1607) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1607_2297 : (Triangular src1607) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1607_2305 : (Triangular src1607) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1607_2327 : (Triangular src1607) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1607_2388 : (Triangular src1607) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1607 : Cover (Triangular src1607) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass1607_2293, by decide, by decide, pass1607_2294, by decide, by decide, pass1607_2297, by decide, by decide, pass1607_2305, by decide, by decide, pass1607_2327, by decide, by decide, pass1607_2388, rfl⟩
def src1608 : Request := ⟨⟨⟨4800,6690,1512,857398⟩,3433136573644800,56816483122989⟩,245,6,1,772091,9⟩
private theorem pass1608_2293 : (Triangular src1608) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1608_2295 : (Triangular src1608) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1608_2300 : (Triangular src1608) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1608_2314 : (Triangular src1608) 2314 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1608_2353 : (Triangular src1608) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1608 : Cover (Triangular src1608) 2389 2293 [2294,2299,2313,2352,2389] := by
  exact ⟨by decide, by decide, pass1608_2293, by decide, by decide, pass1608_2295, by decide, by decide, pass1608_2300, by decide, by decide, pass1608_2314, by decide, by decide, pass1608_2353, rfl⟩
def src1611 : Request := ⟨⟨⟨325,453,100,5419⟩,1061047500800,1193036697⟩,0,6,1,772091,16⟩
private theorem pass1611_2293 : (Triangular src1611) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1611_2295 : (Triangular src1611) 2295 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1611_2302 : (Triangular src1611) 2302 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1611_2327 : (Triangular src1611) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1611 : Cover (Triangular src1611) 2389 2293 [2294,2301,2326,2389] := by
  exact ⟨by decide, by decide, pass1611_2293, by decide, by decide, pass1611_2295, by decide, by decide, pass1611_2302, by decide, by decide, pass1611_2327, rfl⟩
def src1612 : Request := ⟨⟨⟨400,558,120,6858⟩,1935519252480,2682384904⟩,2,6,1,772091,16⟩
private theorem pass1612_2293 : (Triangular src1612) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1612_2300 : (Triangular src1612) 2300 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1612_2324 : (Triangular src1612) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1612 : Cover (Triangular src1612) 2389 2293 [2299,2323,2389] := by
  exact ⟨by decide, by decide, pass1612_2293, by decide, by decide, pass1612_2300, by decide, by decide, pass1612_2324, rfl⟩
def src1613 : Request := ⟨⟨⟨470,655,144,7715⟩,3184589537280,5168862572⟩,4,6,1,772091,16⟩
private theorem pass1613_2293 : (Triangular src1613) 2293 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1613_2313 : (Triangular src1613) 2313 2378 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1613_2379 : (Triangular src1613) 2379 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1613 : Cover (Triangular src1613) 2389 2293 [2312,2378,2389] := by
  exact ⟨by decide, by decide, pass1613_2293, by decide, by decide, pass1613_2313, by decide, by decide, pass1613_2379, rfl⟩
def src1614 : Request := ⟨⟨⟨560,781,172,9763⟩,5388141854720,10440670587⟩,8,6,1,772091,16⟩
private theorem pass1614_2293 : (Triangular src1614) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1614_2298 : (Triangular src1614) 2298 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1614_2314 : (Triangular src1614) 2314 2363 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1614_2364 : (Triangular src1614) 2364 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1614 : Cover (Triangular src1614) 2389 2293 [2297,2313,2363,2389] := by
  exact ⟨by decide, by decide, pass1614_2293, by decide, by decide, pass1614_2298, by decide, by decide, pass1614_2314, by decide, by decide, pass1614_2364, rfl⟩
def src1615 : Request := ⟨⟨⟨825,1150,253,17590⟩,17161575202816,48873782027⟩,20,6,1,772091,16⟩
private theorem pass1615_2293 : (Triangular src1615) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1615_2301 : (Triangular src1615) 2301 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1615_2325 : (Triangular src1615) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1615 : Cover (Triangular src1615) 2389 2293 [2300,2324,2389] := by
  exact ⟨by decide, by decide, pass1615_2293, by decide, by decide, pass1615_2301, by decide, by decide, pass1615_2325, rfl⟩
def src1616 : Request := ⟨⟨⟨1450,2022,445,28173⟩,92998964346880,465769321795⟩,40,6,1,772091,16⟩
private theorem pass1616_2293 : (Triangular src1616) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1616_2306 : (Triangular src1616) 2306 2343 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1616_2344 : (Triangular src1616) 2344 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1616 : Cover (Triangular src1616) 2389 2293 [2305,2343,2389] := by
  exact ⟨by decide, by decide, pass1616_2293, by decide, by decide, pass1616_2306, by decide, by decide, pass1616_2344, rfl⟩
def src1617 : Request := ⟨⟨⟨1450,2021,445,164837⟩,92998964346880,465028319332⟩,65,6,1,772091,16⟩
private theorem pass1617_2293 : (Triangular src1617) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1617_2297 : (Triangular src1617) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1617_2308 : (Triangular src1617) 2308 2339 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1617_2340 : (Triangular src1617) 2340 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1617 : Cover (Triangular src1617) 2389 2293 [2296,2307,2339,2389] := by
  exact ⟨by decide, by decide, pass1617_2293, by decide, by decide, pass1617_2297, by decide, by decide, pass1617_2308, by decide, by decide, pass1617_2340, rfl⟩
def src1618 : Request := ⟨⟨⟨2600,3625,783,57109⟩,527755772952576,4733203574232⟩,85,6,1,772091,16⟩
private theorem pass1618_2293 : (Triangular src1618) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1618_2295 : (Triangular src1618) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1618_2301 : (Triangular src1618) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1618_2318 : (Triangular src1618) 2318 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1618_2366 : (Triangular src1618) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1618 : Cover (Triangular src1618) 2389 2293 [2294,2300,2317,2365,2389] := by
  exact ⟨by decide, by decide, pass1618_2293, by decide, by decide, pass1618_2295, by decide, by decide, pass1618_2301, by decide, by decide, pass1618_2318, by decide, by decide, pass1618_2366, rfl⟩
def src1619 : Request := ⟨⟨⟨4800,6690,1474,762132⟩,3367547627110400,55703383755931⟩,245,6,1,772091,16⟩
private theorem pass1619_2293 : (Triangular src1619) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1619_2294 : (Triangular src1619) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1619_2296 : (Triangular src1619) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1619_2302 : (Triangular src1619) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1619_2319 : (Triangular src1619) 2319 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1619_2365 : (Triangular src1619) 2365 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1619 : Cover (Triangular src1619) 2389 2293 [2293,2295,2301,2318,2364,2389] := by
  exact ⟨by decide, by decide, pass1619_2293, by decide, by decide, pass1619_2294, by decide, by decide, pass1619_2296, by decide, by decide, pass1619_2302, by decide, by decide, pass1619_2319, by decide, by decide, pass1619_2365, rfl⟩
def src1620 : Request := ⟨⟨⟨6900,9621,2118,146522⟩,9997036108906496,238016971510476⟩,245,6,1,772091,16⟩
private theorem pass1620_2293 : (Triangular src1620) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1620_2298 : (Triangular src1620) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1620_2312 : (Triangular src1620) 2312 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1620_2351 : (Triangular src1620) 2351 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1620 : Cover (Triangular src1620) 2389 2293 [2297,2311,2350,2389] := by
  exact ⟨by decide, by decide, pass1620_2293, by decide, by decide, pass1620_2298, by decide, by decide, pass1620_2312, by decide, by decide, pass1620_2351, rfl⟩
def src1621 : Request := ⟨⟨⟨8300,11575,2615,130242⟩,17745461310914560,508734991702659⟩,245,6,1,772091,16⟩
private theorem pass1621_2293 : (Triangular src1621) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1621_2299 : (Triangular src1621) 2299 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1621_2315 : (Triangular src1621) 2315 2358 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1621_2359 : (Triangular src1621) 2359 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1621 : Cover (Triangular src1621) 2389 2293 [2298,2314,2358,2389] := by
  exact ⟨by decide, by decide, pass1621_2293, by decide, by decide, pass1621_2299, by decide, by decide, pass1621_2315, by decide, by decide, pass1621_2359, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1668

-- Source: Research6969.PrefixRescueDataHigherHelperCases15
section Z6969Source1669
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases15
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,15⟩
  bank i := ![bank100 6858, bank100 7715, bank134 8679, bank142 10983, bank156 13899, bank221 19788, bank234 31694, bank225 102908, bank297 57109, bank339 91474, bank318 857398] i
  reserve i := ![0, 1, 3, 6, 10, 20, 40, 50, 85, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 772091
  seedFloor := 9

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank100 6858
    · exact rank100 7715
    · exact rank134 8679
    · exact rank142 10983
    · exact rank156 13899
    · exact rank221 19788
    · exact rank234 31694
    · exact rank225 102908
    · exact rank297 57109
    · exact rank339 91474
    · exact rank318 857398
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1596⟩
    · exact ⟨_, cover1597⟩
    · exact ⟨_, cover1598⟩
    · exact ⟨_, cover1599⟩
    · exact ⟨_, cover1600⟩
    · exact ⟨_, cover1601⟩
    · exact ⟨_, cover1602⟩
    · exact ⟨_, cover1603⟩
    · exact ⟨_, cover1605⟩
    · exact ⟨_, cover1607⟩
    · exact ⟨_, cover1608⟩

def price : EarlyPrice := ⟨6, 15, 10, 85/100, 80/100, ![5006686451608, 1699136734946, 10487555216, 3495861916], 2317503188220960⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![2375/41, 59207/73, 334047/73, 686055/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases15
end Z6969Source1669

-- Source: Research6969.PrefixNearSavedHigherHelperCases15
section Z6969Source1670
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases15
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4572,57,811,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases15.plan Lower6960.Prefix6969RescueData.HigherHelperCases15.plan Lower6960.Prefix6969RescueData.HigherHelperCases15.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 6 9 15 772091 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases15.plan, Lower6960.Prefix6969MainCases.HigherHelperCases15.price, Lower6960.Prefix6969MainCases.HigherHelperCases15.valid, Lower6960.Prefix6969MainCases.HigherHelperCases15.priced, Lower6960.Prefix6969MainCases.HigherHelperCases15.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases15.plan, Lower6960.Prefix6969RescueData.HigherHelperCases15.price, Lower6960.Prefix6969RescueData.HigherHelperCases15.sources, Lower6960.Prefix6969RescueData.HigherHelperCases15.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 195335397543475100 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases15
end Z6969Source1670

-- Source: Research6969.PrefixMainDataHigherHelperCases16
section Z6969Source1671
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases16
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 16
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 13, 21, 25, 40, 40, 65, 75, 105, 75, 75] i
  bank i := ![bank3 1490, bank10 1603, bank19 1656, bank24 1838, bank33 1882, bank42 2171, bank55 2427, bank72 2841, bank108 3859, bank103 5586, bank124 22589, bank159 6076, bank199 9241, bank187 32183, bank230 14067, bank172 88577, bank171 201573] i
  head := src1764
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15703, 163063, 752596, 3392981],
    ![24861/2, 238315/2, 1086533/2, 2569609],
    ![6218, 57110, 1086533/2, 2347380],
    ![29433/8, 278135/8, 2518916/9, 1157940],
    ![65616/25, 23684, 203256, 885481],
    ![73478/49, 675250/49, 3042482/25, 4713241/9],
    ![45497/50, 39624/5, 361623/4, 5890329/16],
    ![45497/50, 39624/5, 2142741/25, 8071281/25],
    ![76938/121, 668926/121, 1863897/32, 1562895/7],
    ![76938/121, 668926/121, 1863897/32, 1562895/7],
    ![20667/50, 668926/121, 1863897/32, 1562895/7],
    ![20667/50, 202517/40, 48422, 188356],
    ![20667/50, 6033640/1323, 20388273/484, 78594705/484],
    ![1960504/5329, 6033640/1323, 20388273/484, 78594705/484],
    ![1960504/5329, 75300/17, 49206366/1225, 797598900/5041],
    ![1872696/5329, 75300/17, 49206366/1225, 797598900/5041],
    ![1826342/5329, 75300/17, 49206366/1225, 797598900/5041]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 6 16 772091 := by
  refine ⟨?_, rank154 5670, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1764⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free19_0
    · exact free24_0
    · exact free33_0
    · exact free42_0
    · exact free55_0
    · exact free72_0
    · exact free108_0
    · exact free103_1
    · exact free124_0
    · exact free159_0
    · exact free199_0
    · exact free187_0
    · exact free230_0
    · exact free172_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [315141256, 314531187, 314435749, 314573787, 315124664, 313078545, 160002366, 159978211, 56282923, 72574561, 72387183, 81739552, 85751918, 119925918, 99052906, 137301994, 232619152], [1112865, 1115986, 1116474, 1115768, 1112949, 1123417, 2400576, 2400977, 7174745, 5521491, 5536383, 4878685, 4640432, 3265576, 3994624, 2829093, 1591100],
  ![123478898264640, 1608508997168, 209357236800, 5551479200], 172048407349463220⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 75300/17, 49206366/1225, 797598900/5041] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases16
end Z6969Source1671

-- Source: Research6969.PrefixRescueDataHigherHelperCases16
section Z6969Source1672
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases16
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,25⟩
  bank i := ![bank101 5419, bank133 6858, bank142 7715, bank156 9763, bank201 17590, bank233 28173, bank261 57109, bank231 164837, bank363 130242, bank317 762132, bank349 146522] i
  reserve i := ![0, 2, 4, 8, 20, 40, 85, 65, 245, 245, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 772091
  seedFloor := 16

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 5419
    · exact rank133 6858
    · exact rank142 7715
    · exact rank156 9763
    · exact rank201 17590
    · exact rank233 28173
    · exact rank261 57109
    · exact rank231 164837
    · exact rank363 130242
    · exact rank317 762132
    · exact rank349 146522
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1611⟩
    · exact ⟨_, cover1612⟩
    · exact ⟨_, cover1613⟩
    · exact ⟨_, cover1614⟩
    · exact ⟨_, cover1615⟩
    · exact ⟨_, cover1616⟩
    · exact ⟨_, cover1618⟩
    · exact ⟨_, cover1617⟩
    · exact ⟨_, cover1621⟩
    · exact ⟨_, cover1619⟩
    · exact ⟨_, cover1620⟩

def price : EarlyPrice := ⟨6, 25, 10, 75/100, 70/100, ![7417314792636, 1534231632940, 25450024645, 5090021665], 2444489377432612⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![7030/123, 195617/246, 1070827/246, 542675/41] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases16
end Z6969Source1672

-- Source: Research6969.PrefixNearSavedHigherHelperCases16
section Z6969Source1673
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases16
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4429,57,795,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases16.plan Lower6960.Prefix6969RescueData.HigherHelperCases16.plan Lower6960.Prefix6969RescueData.HigherHelperCases16.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 6 16 25 772091 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases16.plan, Lower6960.Prefix6969MainCases.HigherHelperCases16.price, Lower6960.Prefix6969MainCases.HigherHelperCases16.valid, Lower6960.Prefix6969MainCases.HigherHelperCases16.priced, Lower6960.Prefix6969MainCases.HigherHelperCases16.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases16.plan, Lower6960.Prefix6969RescueData.HigherHelperCases16.price, Lower6960.Prefix6969RescueData.HigherHelperCases16.sources, Lower6960.Prefix6969RescueData.HigherHelperCases16.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 208369786287770503 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases16
end Z6969Source1673

-- Source: Research6969.PrefixMainDataMarkedExitCandidates0
section Z6969Source1674
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.MarkedExitCandidates0
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 11
  reserve i := ![0, 1, 2, 3, 5, 8, 12, 21, 30, 65, 65, 75] i
  bank i := ![bank3 1490, bank10 1603, bank19 1656, bank24 1838, bank37 2039, bank50 2450, bank63 2899, bank108 3859, bank139 4862, bank167 24691, bank199 9241, bank171 201573] i
  head := src1765
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8]
  historyValues := [![16039, 161603, 742684, 3347560],
    ![24861/2, 229369/2, 528990, 2569609],
    ![6218, 493613/9, 528990, 2141622],
    ![29433/8, 534899/16, 2422498/9, 9507974/9],
    ![17323/9, 610453/36, 2748379/16, 10547747/16],
    ![81680/81, 726880/81, 91049, 1500625/4],
    ![81680/81, 726880/81, 91049, 29993054/81],
    ![76938/121, 642088/121, 5477707/98, 2851801/14],
    ![76938/121, 780553/150, 556920/11, 37726689/200],
    ![55840/147, 780553/150, 556920/11, 37726689/200],
    ![55840/147, 5780170/1323, 39078297/968, 286822158/1849],
    ![1826342/5329, 5780170/1323, 39078297/968, 286822158/1849]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 6 26 772091 := by
  refine ⟨?_, rank154 5173, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1765⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free19_0
    · exact free24_0
    · exact free37_0
    · exact free50_0
    · exact free63_0
    · exact free108_0
    · exact free139_0
    · exact free167_0
    · exact free199_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [306511033, 305437027, 305531502, 305284595, 306197049, 147285048, 147271224, 111053365, 90172940, 90096752, 143021696, 232602229], [1157015, 1162509, 1162026, 1163289, 1158621, 2612017, 2612247, 3541452, 4406610, 4410452, 2703690, 1591239],
  ![123469915197780, 1608527206016, 209342006100, 4498661040], 168003688186988620⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 10 _
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

theorem final_cap : plan.history plan.last = ![1826342/5329, 5780170/1323, 39078297/968, 286822158/1849] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.MarkedExitCandidates0
end Z6969Source1674

-- Source: Research6969.PhysicalChecks109
section Z6969Source1675
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1628 : Request := ⟨⟨⟨275,383,83,4817⟩,635228389376,603020643⟩,0,6,1,772091,26⟩
private theorem pass1628_2293 : (Triangular src1628) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1628_2294 : (Triangular src1628) 2294 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1628_2298 : (Triangular src1628) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1628_2313 : (Triangular src1628) 2313 2370 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1628_2371 : (Triangular src1628) 2371 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1628 : Cover (Triangular src1628) 2389 2293 [2293,2297,2312,2370,2389] := by
  exact ⟨by decide, by decide, pass1628_2293, by decide, by decide, pass1628_2294, by decide, by decide, pass1628_2298, by decide, by decide, pass1628_2313, by decide, by decide, pass1628_2371, rfl⟩
def src1629 : Request := ⟨⟨⟨325,453,100,4817⟩,1061047500800,1193036697⟩,1,6,1,772091,26⟩
private theorem pass1629_2293 : (Triangular src1629) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1629_2299 : (Triangular src1629) 2299 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1629_2320 : (Triangular src1629) 2320 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1629 : Cover (Triangular src1629) 2389 2293 [2298,2319,2389] := by
  exact ⟨by decide, by decide, pass1629_2293, by decide, by decide, pass1629_2299, by decide, by decide, pass1629_2320, rfl⟩
def src1630 : Request := ⟨⟨⟨400,558,120,6858⟩,1935519252480,2682384904⟩,4,6,1,772091,26⟩
private theorem pass1630_2293 : (Triangular src1630) 2293 2309 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1630_2310 : (Triangular src1630) 2310 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1630_2368 : (Triangular src1630) 2368 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1630 : Cover (Triangular src1630) 2389 2293 [2309,2367,2389] := by
  exact ⟨by decide, by decide, pass1630_2293, by decide, by decide, pass1630_2310, by decide, by decide, pass1630_2368, rfl⟩
def src1631 : Request := ⟨⟨⟨470,655,144,8679⟩,3184589537280,5168862572⟩,8,6,1,772091,26⟩
private theorem pass1631_2293 : (Triangular src1631) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1631_2300 : (Triangular src1631) 2300 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1631_2323 : (Triangular src1631) 2323 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1631 : Cover (Triangular src1631) 2389 2293 [2299,2322,2389] := by
  exact ⟨by decide, by decide, pass1631_2293, by decide, by decide, pass1631_2300, by decide, by decide, pass1631_2323, rfl⟩
def src1632 : Request := ⟨⟨⟨690,962,212,12355⟩,10065769922560,23997864317⟩,16,6,1,772091,26⟩
private theorem pass1632_2293 : (Triangular src1632) 2293 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1632_2308 : (Triangular src1632) 2308 2353 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1632_2354 : (Triangular src1632) 2354 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1632 : Cover (Triangular src1632) 2389 2293 [2307,2353,2389] := by
  exact ⟨by decide, by decide, pass1632_2293, by decide, by decide, pass1632_2308, by decide, by decide, pass1632_2354, rfl⟩
def src1633 : Request := ⟨⟨⟨1000,1394,307,22261⟩,30557599170560,105471636407⟩,32,6,1,772091,26⟩
private theorem pass1633_2293 : (Triangular src1633) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1633_2295 : (Triangular src1633) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1633_2301 : (Triangular src1633) 2301 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1633_2319 : (Triangular src1633) 2319 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1633_2372 : (Triangular src1633) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1633 : Cover (Triangular src1633) 2389 2293 [2294,2300,2318,2371,2389] := by
  exact ⟨by decide, by decide, pass1633_2293, by decide, by decide, pass1633_2295, by decide, by decide, pass1633_2301, by decide, by decide, pass1633_2319, by decide, by decide, pass1633_2372, rfl⟩
def src1634 : Request := ⟨⟨⟨1750,2440,537,25043⟩,163381988556800,986966790957⟩,50,6,1,772091,26⟩
private theorem pass1634_2293 : (Triangular src1634) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1634_2295 : (Triangular src1634) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1634_2300 : (Triangular src1634) 2300 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1634_2315 : (Triangular src1634) 2315 2357 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1634_2358 : (Triangular src1634) 2358 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1634 : Cover (Triangular src1634) 2389 2293 [2294,2299,2314,2357,2389] := by
  exact ⟨by decide, by decide, pass1634_2293, by decide, by decide, pass1634_2295, by decide, by decide, pass1634_2300, by decide, by decide, pass1634_2315, by decide, by decide, pass1634_2358, rfl⟩
def src1635 : Request := ⟨⟨⟨1450,2021,445,115771⟩,92998964346880,465028319332⟩,65,6,1,772091,26⟩
private theorem pass1635_2293 : (Triangular src1635) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1635_2295 : (Triangular src1635) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1635_2300 : (Triangular src1635) 2300 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1635_2315 : (Triangular src1635) 2315 2357 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1635_2358 : (Triangular src1635) 2358 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1635 : Cover (Triangular src1635) 2389 2293 [2294,2299,2314,2357,2389] := by
  exact ⟨by decide, by decide, pass1635_2293, by decide, by decide, pass1635_2295, by decide, by decide, pass1635_2300, by decide, by decide, pass1635_2315, by decide, by decide, pass1635_2358, rfl⟩
def src1636 : Request := ⟨⟨⟨2600,3625,819,40111⟩,546063062138880,4901614794409⟩,85,6,1,772091,26⟩
private theorem pass1636_2293 : (Triangular src1636) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1636_2294 : (Triangular src1636) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1636_2296 : (Triangular src1636) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1636_2302 : (Triangular src1636) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1636_2319 : (Triangular src1636) 2319 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1636_2366 : (Triangular src1636) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1636 : Cover (Triangular src1636) 2389 2293 [2293,2295,2301,2318,2365,2389] := by
  exact ⟨by decide, by decide, pass1636_2293, by decide, by decide, pass1636_2294, by decide, by decide, pass1636_2296, by decide, by decide, pass1636_2302, by decide, by decide, pass1636_2319, by decide, by decide, pass1636_2366, rfl⟩
def src1637 : Request := ⟨⟨⟨4800,6690,1512,535271⟩,3433136573644800,56816483122989⟩,245,6,1,772091,26⟩
private theorem pass1637_2293 : (Triangular src1637) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1637_2296 : (Triangular src1637) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1637_2304 : (Triangular src1637) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1637_2326 : (Triangular src1637) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1637_2387 : (Triangular src1637) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1637 : Cover (Triangular src1637) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass1637_2293, by decide, by decide, pass1637_2296, by decide, by decide, pass1637_2304, by decide, by decide, pass1637_2326, by decide, by decide, pass1637_2387, rfl⟩
def src1638 : Request := ⟨⟨⟨6900,9621,2118,115771⟩,9997036108906496,238016971510476⟩,245,6,1,772091,26⟩
private theorem pass1638_2293 : (Triangular src1638) 2293 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1638_2309 : (Triangular src1638) 2309 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1638_2353 : (Triangular src1638) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1638 : Cover (Triangular src1638) 2389 2293 [2308,2352,2389] := by
  exact ⟨by decide, by decide, pass1638_2293, by decide, by decide, pass1638_2309, by decide, by decide, pass1638_2353, rfl⟩
def src1643 : Request := ⟨⟨⟨275,383,83,3384⟩,635228389376,603020643⟩,0,6,1,772091,41⟩
private theorem pass1643_2293 : (Triangular src1643) 2293 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1643_2332 : (Triangular src1643) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1643 : Cover (Triangular src1643) 2389 2293 [2331,2389] := by
  exact ⟨by decide, by decide, pass1643_2293, by decide, by decide, pass1643_2332, rfl⟩
def src1644 : Request := ⟨⟨⟨325,453,98,3384⟩,1045036793856,1174588250⟩,1,6,1,772091,41⟩
private theorem pass1644_2293 : (Triangular src1644) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1644_2296 : (Triangular src1644) 2296 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1644_2307 : (Triangular src1644) 2307 2346 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1644_2347 : (Triangular src1644) 2347 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1644 : Cover (Triangular src1644) 2389 2293 [2295,2306,2346,2389] := by
  exact ⟨by decide, by decide, pass1644_2293, by decide, by decide, pass1644_2296, by decide, by decide, pass1644_2307, by decide, by decide, pass1644_2347, rfl⟩
def src1645 : Request := ⟨⟨⟨325,453,98,3807⟩,1045036793856,1174588250⟩,2,6,1,772091,41⟩
private theorem pass1645_2293 : (Triangular src1645) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1645_2294 : (Triangular src1645) 2294 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1645_2298 : (Triangular src1645) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1645_2312 : (Triangular src1645) 2312 2362 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1645_2363 : (Triangular src1645) 2363 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1645 : Cover (Triangular src1645) 2389 2293 [2293,2297,2311,2362,2389] := by
  exact ⟨by decide, by decide, pass1645_2293, by decide, by decide, pass1645_2294, by decide, by decide, pass1645_2298, by decide, by decide, pass1645_2312, by decide, by decide, pass1645_2363, rfl⟩
def src1646 : Request := ⟨⟨⟨325,453,100,4282⟩,1061047500800,1193036697⟩,3,6,1,772091,41⟩
private theorem pass1646_2293 : (Triangular src1646) 2293 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1646_2304 : (Triangular src1646) 2304 2342 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1646_2343 : (Triangular src1646) 2343 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1646 : Cover (Triangular src1646) 2389 2293 [2303,2342,2389] := by
  exact ⟨by decide, by decide, pass1646_2293, by decide, by decide, pass1646_2304, by decide, by decide, pass1646_2343, rfl⟩
def src1647 : Request := ⟨⟨⟨400,558,123,5419⟩,1971918995456,2734096379⟩,6,6,1,772091,41⟩
private theorem pass1647_2293 : (Triangular src1647) 2293 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1647_2316 : (Triangular src1647) 2316 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1647 : Cover (Triangular src1647) 2389 2293 [2315,2389] := by
  exact ⟨by decide, by decide, pass1647_2293, by decide, by decide, pass1647_2316, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1675

-- Source: Research6969.PrefixRescueDataMarkedExitCandidates0
section Z6969Source1676
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.MarkedExitCandidates0
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,40⟩
  bank i := ![bank78 4817, bank101 4817, bank133 6858, bank142 8679, bank193 12355, bank218 22261, bank240 25043, bank231 115771, bank263 40111, bank349 115771, bank318 535271] i
  reserve i := ![0, 1, 4, 8, 16, 32, 50, 65, 85, 245, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 772091
  seedFloor := 26

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank78 4817
    · exact rank101 4817
    · exact rank133 6858
    · exact rank142 8679
    · exact rank193 12355
    · exact rank218 22261
    · exact rank240 25043
    · exact rank231 115771
    · exact rank263 40111
    · exact rank349 115771
    · exact rank318 535271
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1628⟩
    · exact ⟨_, cover1629⟩
    · exact ⟨_, cover1630⟩
    · exact ⟨_, cover1631⟩
    · exact ⟨_, cover1632⟩
    · exact ⟨_, cover1633⟩
    · exact ⟨_, cover1634⟩
    · exact ⟨_, cover1635⟩
    · exact ⟨_, cover1636⟩
    · exact ⟨_, cover1638⟩
    · exact ⟨_, cover1637⟩

def price : EarlyPrice := ⟨6, 40, 10, 70/100, 60/100, ![8335086924494, 1122519813733, 32980890252, 4122625578], 2239889351745686⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![2375/41, 200491/246, 179911/41, 802220/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.MarkedExitCandidates0
end Z6969Source1676

-- Source: Research6969.PrefixNearSavedMarkedExitCandidates0
section Z6969Source1677
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedMarkedExitCandidates0
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4368,57,815,true⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.MarkedExitCandidates0.plan Lower6960.Prefix6969RescueData.MarkedExitCandidates0.plan Lower6960.Prefix6969RescueData.MarkedExitCandidates0.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  exact ⟨by decide, by decide +kernel⟩

def data : NearCase 6 26 40 772091 :=
  ⟨Lower6960.Prefix6969MainCases.MarkedExitCandidates0.plan, Lower6960.Prefix6969MainCases.MarkedExitCandidates0.price, Lower6960.Prefix6969MainCases.MarkedExitCandidates0.valid, Lower6960.Prefix6969MainCases.MarkedExitCandidates0.priced, Lower6960.Prefix6969MainCases.MarkedExitCandidates0.sources,
   Lower6960.Prefix6969RescueData.MarkedExitCandidates0.plan, Lower6960.Prefix6969RescueData.MarkedExitCandidates0.price, Lower6960.Prefix6969RescueData.MarkedExitCandidates0.sources, Lower6960.Prefix6969RescueData.MarkedExitCandidates0.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 219802581133534479 := by
  unfold NearCase.fee
  unfold Exit.extra
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedMarkedExitCandidates0
end Z6969Source1677

-- Source: Research6969.PrefixMainDataMarkedExitCandidates1
section Z6969Source1678
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.MarkedExitCandidates1
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 9, 13, 15, 21, 30, 40, 40, 65, 65, 105, 75, 75] i
  bank i := ![bank3 1490, bank11 1580, bank19 1656, bank24 1838, bank33 1882, bank37 2039, bank45 2316, bank55 2427, bank72 2841, bank65 3612, bank123 3616, bank168 4492, bank136 13749, bank159 6076, bank199 9241, bank167 24691, bank230 14067, bank172 88577, bank171 201573] i
  head := src1766
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15979, 158278, 724552, 3157380],
    ![12581, 218549/2, 521400, 2496400],
    ![6218, 52026, 521400, 1885356],
    ![29433/8, 254141/8, 2302412/9, 930028],
    ![65616/25, 538532/25, 203256, 885481],
    ![17323/9, 144721/9, 1303933/8, 4642803/8],
    ![38747/32, 326649/32, 2944668/25, 10547064/25],
    ![45497/50, 179427/25, 269228/3, 614031/2],
    ![45497/50, 179427/25, 2096658/25, 614031/2],
    ![13307/16, 179427/25, 8764728/121, 614031/2],
    ![84176/121, 602296/121, 2616248/49, 8233632/49],
    ![84176/121, 602296/121, 2616248/49, 7671213/50],
    ![86337/200, 602296/121, 2616248/49, 7671213/50],
    ![86337/200, 182987/40, 32989384/729, 7671213/50],
    ![86337/200, 111520/27, 21050998/529, 7013919/49],
    ![55840/147, 111520/27, 21050998/529, 7013919/49],
    ![55840/147, 4010, 303743/8, 197880489/1444],
    ![1872696/5329, 4010, 303743/8, 197880489/1444],
    ![1826342/5329, 4010, 303743/8, 197880489/1444]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 6 41 772091 := by
  refine ⟨?_, rank154 4554, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1766⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free11_0
    · exact free19_0
    · exact free24_0
    · exact free33_0
    · exact free37_0
    · exact free45_0
    · exact free55_0
    · exact free72_0
    · exact free65_0
    · exact free123_0
    · exact free168_0
    · exact free136_0
    · exact free159_0
    · exact free199_0
    · exact free167_0
    · exact free230_0
    · exact free172_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [291225562, 291013950, 289408217, 289263478, 289818284, 290342834, 290880095, 115201093, 115398663, 114337204, 96818562, 60965618, 56156878, 74477073, 72880497, 118347785, 95727120, 132915894, 229261275], [1235212, 1236295, 1244509, 1245250, 1242411, 1239728, 1236979, 3397655, 3392132, 3427456, 4088925, 6607833, 7190934, 5370284, 5497176, 3309692, 4134990, 2925258, 1618708],
  ![121696469995500, 1612136607660, 206335147500, 5626476400], 157714937181338015⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 19 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 4010, 303743/8, 197880489/1444] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.MarkedExitCandidates1
end Z6969Source1678

-- Source: Research6969.PrefixRescueDataMarkedExitCandidates1
section Z6969Source1679
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.MarkedExitCandidates1
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,56⟩
  bank i := ![bank78 3384, bank100 3384, bank100 3807, bank101 4282, bank134 5419, bank156 7715, bank225 15636, bank231 57109, bank240 25043, bank319 64247, bank318 234698] i
  reserve i := ![0, 1, 2, 3, 6, 13, 40, 65, 65, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 772091
  seedFloor := 41

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank78 3384
    · exact rank100 3384
    · exact rank100 3807
    · exact rank101 4282
    · exact rank134 5419
    · exact rank156 7715
    · exact rank225 15636
    · exact rank231 57109
    · exact rank240 25043
    · exact rank319 64247
    · exact rank318 234698
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1643⟩
    · exact ⟨_, cover1644⟩
    · exact ⟨_, cover1645⟩
    · exact ⟨_, cover1646⟩
    · exact ⟨_, cover1647⟩
    · exact ⟨_, cover1648⟩
    · exact ⟨_, cover1649⟩
    · exact ⟨_, cover1650⟩
    · exact ⟨_, cover1651⟩
    · exact ⟨_, cover1654⟩
    · exact ⟨_, cover1655⟩

def price : EarlyPrice := ⟨6, 56, 10, 65/100, 70/100, ![5116509809804, 569715311602, 32962201776, 2943064152], 1482872690278415⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![2375/41, 146791/191, 760234/191, 3597832/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.MarkedExitCandidates1
end Z6969Source1679

end Merged_Z6969Pack0717

-- merged module Z6969Pack0718
section Merged_Z6969Pack0718

-- Source: Research6969.PrefixNearSavedMarkedExitCandidates1
section Z6969Source1680
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedMarkedExitCandidates1
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4010,57,768,true⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.MarkedExitCandidates1.plan Lower6960.Prefix6969RescueData.MarkedExitCandidates1.plan Lower6960.Prefix6969RescueData.MarkedExitCandidates1.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  exact ⟨by decide, by decide +kernel⟩

def data : NearCase 6 41 56 772091 :=
  ⟨Lower6960.Prefix6969MainCases.MarkedExitCandidates1.plan, Lower6960.Prefix6969MainCases.MarkedExitCandidates1.price, Lower6960.Prefix6969MainCases.MarkedExitCandidates1.valid, Lower6960.Prefix6969MainCases.MarkedExitCandidates1.priced, Lower6960.Prefix6969MainCases.MarkedExitCandidates1.sources,
   Lower6960.Prefix6969RescueData.MarkedExitCandidates1.plan, Lower6960.Prefix6969RescueData.MarkedExitCandidates1.price, Lower6960.Prefix6969RescueData.MarkedExitCandidates1.sources, Lower6960.Prefix6969RescueData.MarkedExitCandidates1.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 206323363435764496 := by
  unfold NearCase.fee
  unfold Exit.extra
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedMarkedExitCandidates1
end Z6969Source1680

-- Source: Research6969.PrefixNearSelect6
section Z6969Source1681
set_option autoImplicit true
namespace Lower6960.Prefix6969Early
set_option maxHeartbeats 8000000

theorem nearChoose6 (j : Fin 56) (ok : UniformAllowed 6 (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧ w≤772091 ∧ ∃ c : NearCase 6 l u w, c.uniform := by
  fin_cases j
  · refine ⟨1, 1, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases12.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases12.fee_exact]; decide +kernel
  · refine ⟨2, 3, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases13.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases13.fee_exact]; decide +kernel
  · refine ⟨2, 3, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases13.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases13.fee_exact]; decide +kernel
  · refine ⟨4, 8, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases14.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases14.fee_exact]; decide +kernel
  · refine ⟨4, 8, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases14.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases14.fee_exact]; decide +kernel
  · refine ⟨4, 8, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases14.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases14.fee_exact]; decide +kernel
  · refine ⟨4, 8, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases14.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases14.fee_exact]; decide +kernel
  · refine ⟨4, 8, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases14.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases14.fee_exact]; decide +kernel
  · refine ⟨9, 15, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases15.fee_exact]; decide +kernel
  · refine ⟨9, 15, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases15.fee_exact]; decide +kernel
  · refine ⟨9, 15, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases15.fee_exact]; decide +kernel
  · refine ⟨9, 15, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases15.fee_exact]; decide +kernel
  · refine ⟨9, 15, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases15.fee_exact]; decide +kernel
  · refine ⟨9, 15, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases15.fee_exact]; decide +kernel
  · refine ⟨9, 15, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases15.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases15.fee_exact]; decide +kernel
  · refine ⟨16, 25, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases16.fee_exact]; decide +kernel
  · refine ⟨16, 25, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases16.fee_exact]; decide +kernel
  · refine ⟨16, 25, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases16.fee_exact]; decide +kernel
  · refine ⟨16, 25, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases16.fee_exact]; decide +kernel
  · refine ⟨16, 25, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases16.fee_exact]; decide +kernel
  · refine ⟨16, 25, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases16.fee_exact]; decide +kernel
  · refine ⟨16, 25, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases16.fee_exact]; decide +kernel
  · refine ⟨16, 25, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases16.fee_exact]; decide +kernel
  · refine ⟨16, 25, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases16.fee_exact]; decide +kernel
  · refine ⟨16, 25, 772091, by decide, by decide, by decide, NearSavedHigherHelperCases16.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases16.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨26, 40, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates0.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel
  · refine ⟨41, 56, 772091, by decide, by decide, by decide, NearSavedMarkedExitCandidates1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates1.fee_exact]; decide +kernel

end Lower6960.Prefix6969Early
end Z6969Source1681

-- Source: Research6969.PrefixMainDataHigherHelperCases17
section Z6969Source1682
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases17
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 65, 105, 75, 75] i
  bank i := ![bank3 1490, bank10 1603, bank19 1656, bank24 1838, bank28 2005, bank37 2039, bank42 2497, bank52 2900, bank65 3612, bank83 5597, bank83 2752, bank123 3616, bank122 24063, bank159 6076, bank199 9241, bank158 51722, bank230 14067, bank172 88577, bank171 201573] i
  head := src1767
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14995, 164041, 756984, 3645777],
    ![24861/2, 246037/2, 2243851/4, 2569609],
    ![6218, 177193/3, 2243851/4, 2524986],
    ![29433/8, 574717/16, 2602142/9, 3736654/3],
    ![62542/25, 621404/25, 411025/2, 4020025/4],
    ![17323/9, 657679/36, 2958581/16, 12435861/16],
    ![36739/32, 188459/16, 1203554/9, 15229203/25],
    ![86036/121, 877237/121, 3964817/49, 17687100/49],
    ![86036/121, 877237/121, 3964817/49, 17687100/49],
    ![254619/484, 60494/9, 1091415/16, 17687100/49],
    ![254619/484, 60494/9, 1091415/16, 8392224/25],
    ![254619/484, 694996/121, 60568, 204304],
    ![41249/100, 694996/121, 60568, 204304],
    ![41249/100, 420049/80, 48422, 189069],
    ![41249/100, 6252430/1323, 10525499/242, 169082577/968],
    ![480716/1323, 6252430/1323, 10525499/242, 169082577/968],
    ![480716/1323, 468245/102, 11959375/288, 5295965/32],
    ![1872696/5329, 468245/102, 11959375/288, 5295965/32],
    ![1826342/5329, 468245/102, 11959375/288, 5295965/32]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 7 1 900773 := by
  refine ⟨?_, rank154 6099, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1767⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free19_0
    · exact free24_0
    · exact free28_0
    · exact free37_0
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free83_1
    · exact free83_0
    · exact free123_0
    · exact free122_0
    · exact free159_0
    · exact free199_0
    · exact free158_0
    · exact free230_0
    · exact free172_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [318894467, 317806646, 317701600, 318163221, 318555395, 317436444, 318846090, 146729087, 147237758, 146834290, 146774223, 70117426, 70138108, 83450312, 82768608, 124550565, 100945136, 139596401, 234370048], [1093664, 1099229, 1099766, 1097405, 1095399, 1101123, 1093911, 2622406, 2612804, 2620100, 2621417, 5716777, 5715133, 4777100, 4817580, 3136299, 3914762, 2778789, 1576704],
  ![124408308879360, 1606617254912, 211735960500, 5331708300], 174882719442297534⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 7 _
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
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 468245/102, 11959375/288, 5295965/32] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases17
end Z6969Source1682

-- Source: Research6969.PhysicalChecks111
section Z6969Source1683
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1688 : Request := ⟨⟨⟨400,558,123,7715⟩,1971918995456,2734096379⟩,4,7,1,900773,1⟩
private theorem pass1688_2293 : (Triangular src1688) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1688_2306 : (Triangular src1688) 2306 2349 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1688_2350 : (Triangular src1688) 2350 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1688 : Cover (Triangular src1688) 2389 2293 [2305,2349,2389] := by
  exact ⟨by decide, by decide, pass1688_2293, by decide, by decide, pass1688_2306, by decide, by decide, pass1688_2350, rfl⟩
def src1689 : Request := ⟨⟨⟨560,781,172,9763⟩,5388141854720,10440670587⟩,8,7,1,900773,1⟩
private theorem pass1689_2293 : (Triangular src1689) 2293 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1689_2309 : (Triangular src1689) 2309 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1689_2360 : (Triangular src1689) 2360 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1689 : Cover (Triangular src1689) 2389 2293 [2308,2359,2389] := by
  exact ⟨by decide, by decide, pass1689_2293, by decide, by decide, pass1689_2309, by decide, by decide, pass1689_2360, rfl⟩
def src1690 : Request := ⟨⟨⟨690,962,212,12355⟩,10065769922560,23997864317⟩,13,7,1,900773,1⟩
private theorem pass1690_2293 : (Triangular src1690) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1690_2306 : (Triangular src1690) 2306 2345 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1690_2346 : (Triangular src1690) 2346 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1690 : Cover (Triangular src1690) 2389 2293 [2305,2345,2389] := by
  exact ⟨by decide, by decide, pass1690_2293, by decide, by decide, pass1690_2306, by decide, by decide, pass1690_2346, rfl⟩
def src1691 : Request := ⟨⟨⟨1000,1395,315,15636⟩,31157463285760,107844841957⟩,20,7,1,900773,1⟩
private theorem pass1691_2293 : (Triangular src1691) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1691_2295 : (Triangular src1691) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1691_2301 : (Triangular src1691) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1691_2318 : (Triangular src1691) 2318 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1691_2368 : (Triangular src1691) 2368 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1691 : Cover (Triangular src1691) 2389 2293 [2294,2300,2317,2367,2389] := by
  exact ⟨by decide, by decide, pass1691_2293, by decide, by decide, pass1691_2295, by decide, by decide, pass1691_2301, by decide, by decide, pass1691_2318, by decide, by decide, pass1691_2368, rfl⟩
def src1692 : Request := ⟨⟨⟨1200,1673,368,22261⟩,52718727069696,218387554859⟩,32,7,1,900773,1⟩
private theorem pass1692_2293 : (Triangular src1692) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1692_2298 : (Triangular src1692) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1692_2313 : (Triangular src1692) 2313 2356 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1692_2357 : (Triangular src1692) 2357 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1692 : Cover (Triangular src1692) 2389 2293 [2297,2312,2356,2389] := by
  exact ⟨by decide, by decide, pass1692_2293, by decide, by decide, pass1692_2298, by decide, by decide, pass1692_2313, by decide, by decide, pass1692_2357, rfl⟩
def src1693 : Request := ⟨⟨⟨1750,2440,537,31694⟩,163381988556800,986966790957⟩,50,7,1,900773,1⟩
private theorem pass1693_2293 : (Triangular src1693) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1693_2301 : (Triangular src1693) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1693_2324 : (Triangular src1693) 2324 2388 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1693_2389 : (Triangular src1693) 2389 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1693 : Cover (Triangular src1693) 2389 2293 [2300,2323,2388,2389] := by
  exact ⟨by decide, by decide, pass1693_2293, by decide, by decide, pass1693_2301, by decide, by decide, pass1693_2324, by decide, by decide, pass1693_2389, rfl⟩
def src1694 : Request := ⟨⟨⟨3200,4462,982,64247⟩,997767489781760,11020095796464⟩,110,7,1,900773,1⟩
private theorem pass1694_2293 : (Triangular src1694) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1694_2298 : (Triangular src1694) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1694_2312 : (Triangular src1694) 2312 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1694_2351 : (Triangular src1694) 2351 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1694 : Cover (Triangular src1694) 2389 2293 [2297,2311,2350,2389] := by
  exact ⟨by decide, by decide, pass1694_2293, by decide, by decide, pass1694_2298, by decide, by decide, pass1694_2312, by decide, by decide, pass1694_2351, rfl⟩
def src1695 : Request := ⟨⟨⟨8300,11575,2615,130242⟩,17745461310914560,508734991702659⟩,245,7,1,900773,1⟩
private theorem pass1695_2293 : (Triangular src1695) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1695_2295 : (Triangular src1695) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1695_2300 : (Triangular src1695) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1695_2314 : (Triangular src1695) 2314 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1695_2352 : (Triangular src1695) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1695 : Cover (Triangular src1695) 2389 2293 [2294,2299,2313,2351,2389] := by
  exact ⟨by decide, by decide, pass1695_2293, by decide, by decide, pass1695_2295, by decide, by decide, pass1695_2300, by decide, by decide, pass1695_2314, by decide, by decide, pass1695_2352, rfl⟩
def src1696 : Request := ⟨⟨⟨325,453,100,5419⟩,1061047500800,1193036697⟩,0,7,1,900773,2⟩
private theorem pass1696_2293 : (Triangular src1696) 2293 2309 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1696_2310 : (Triangular src1696) 2310 2370 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1696_2371 : (Triangular src1696) 2371 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1696 : Cover (Triangular src1696) 2389 2293 [2309,2370,2389] := by
  exact ⟨by decide, by decide, pass1696_2293, by decide, by decide, pass1696_2310, by decide, by decide, pass1696_2371, rfl⟩
def src1697 : Request := ⟨⟨⟨325,453,98,6096⟩,1045036793856,1174588250⟩,1,7,1,900773,2⟩
private theorem pass1697_2293 : (Triangular src1697) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1697_2300 : (Triangular src1697) 2300 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1697_2325 : (Triangular src1697) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1697 : Cover (Triangular src1697) 2389 2293 [2299,2324,2389] := by
  exact ⟨by decide, by decide, pass1697_2293, by decide, by decide, pass1697_2300, by decide, by decide, pass1697_2325, rfl⟩
def src1698 : Request := ⟨⟨⟨325,453,98,7715⟩,1045036793856,1174588250⟩,3,7,1,900773,2⟩
private theorem pass1698_2293 : (Triangular src1698) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1698_2297 : (Triangular src1698) 2297 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1698_2312 : (Triangular src1698) 2312 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1698_2366 : (Triangular src1698) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1698 : Cover (Triangular src1698) 2389 2293 [2296,2311,2365,2389] := by
  exact ⟨by decide, by decide, pass1698_2293, by decide, by decide, pass1698_2297, by decide, by decide, pass1698_2312, by decide, by decide, pass1698_2366, rfl⟩
def src1699 : Request := ⟨⟨⟨470,655,148,9763⟩,3250957582336,5279398867⟩,8,7,1,900773,2⟩
private theorem pass1699_2293 : (Triangular src1699) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1699_2298 : (Triangular src1699) 2298 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1699_2314 : (Triangular src1699) 2314 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1699_2366 : (Triangular src1699) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1699 : Cover (Triangular src1699) 2389 2293 [2297,2313,2365,2389] := by
  exact ⟨by decide, by decide, pass1699_2293, by decide, by decide, pass1699_2298, by decide, by decide, pass1699_2314, by decide, by decide, pass1699_2366, rfl⟩
def src1700 : Request := ⟨⟨⟨690,962,208,12355⟩,9921631092736,23645774460⟩,13,7,1,900773,2⟩
private theorem pass1700_2293 : (Triangular src1700) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1700_2294 : (Triangular src1700) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1700_2297 : (Triangular src1700) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1700_2306 : (Triangular src1700) 2306 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1700_2334 : (Triangular src1700) 2334 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1700 : Cover (Triangular src1700) 2389 2293 [2293,2296,2305,2333,2389] := by
  exact ⟨by decide, by decide, pass1700_2293, by decide, by decide, pass1700_2294, by decide, by decide, pass1700_2297, by decide, by decide, pass1700_2306, by decide, by decide, pass1700_2334, rfl⟩
def src1701 : Request := ⟨⟨⟨825,1150,260,15636⟩,17518948515840,49918096074⟩,20,7,1,900773,2⟩
private theorem pass1701_2293 : (Triangular src1701) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1701_2297 : (Triangular src1701) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1701_2309 : (Triangular src1701) 2309 2344 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1701_2345 : (Triangular src1701) 2345 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1701 : Cover (Triangular src1701) 2389 2293 [2296,2308,2344,2389] := by
  exact ⟨by decide, by decide, pass1701_2293, by decide, by decide, pass1701_2297, by decide, by decide, pass1701_2309, by decide, by decide, pass1701_2345, rfl⟩
def src1702 : Request := ⟨⟨⟨1750,2440,537,31694⟩,163381988556800,986966790957⟩,50,7,1,900773,2⟩
private theorem pass1702_2293 : (Triangular src1702) 2293 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1702_2309 : (Triangular src1702) 2309 2353 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1702_2354 : (Triangular src1702) 2354 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1702 : Cover (Triangular src1702) 2389 2293 [2308,2353,2389] := by
  exact ⟨by decide, by decide, pass1702_2293, by decide, by decide, pass1702_2309, by decide, by decide, pass1702_2354, rfl⟩
def src1703 : Request := ⟨⟨⟨1750,2439,537,91474⟩,163381988556800,985665319192⟩,85,7,1,900773,2⟩
private theorem pass1703_2293 : (Triangular src1703) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1703_2298 : (Triangular src1703) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1703_2312 : (Triangular src1703) 2312 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1703_2352 : (Triangular src1703) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1703 : Cover (Triangular src1703) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass1703_2293, by decide, by decide, pass1703_2298, by decide, by decide, pass1703_2312, by decide, by decide, pass1703_2352, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1683

-- Source: Research6969.PrefixRescueDataHigherHelperCases17
section Z6969Source1684
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases17
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,1⟩
  bank i := ![bank101 5419, bank101 6096, bank100 6858, bank134 7715, bank156 9763, bank193 12355, bank223 15636, bank224 22261, bank240 31694, bank296 64247, bank363 130242] i
  reserve i := ![0, 1, 2, 4, 8, 13, 20, 32, 50, 110, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900773
  seedFloor := 1

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 5419
    · exact rank101 6096
    · exact rank100 6858
    · exact rank134 7715
    · exact rank156 9763
    · exact rank193 12355
    · exact rank223 15636
    · exact rank224 22261
    · exact rank240 31694
    · exact rank296 64247
    · exact rank363 130242
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1685⟩
    · exact ⟨_, cover1686⟩
    · exact ⟨_, cover1687⟩
    · exact ⟨_, cover1688⟩
    · exact ⟨_, cover1689⟩
    · exact ⟨_, cover1690⟩
    · exact ⟨_, cover1691⟩
    · exact ⟨_, cover1692⟩
    · exact ⟨_, cover1693⟩
    · exact ⟨_, cover1694⟩
    · exact ⟨_, cover1695⟩

def price : EarlyPrice := ⟨7, 1, 10, 95/100, 80/100, ![50702819874, 307702676008, 1018011655, 6108022860], 430865582551182⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![10354/111, 132857/246, 923269/246, 21707/41] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases17
end Z6969Source1684

-- Source: Research6969.PrefixNearSavedHigherHelperCases17
section Z6969Source1685
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases17
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4590,93,540,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases17.plan Lower6960.Prefix6969RescueData.HigherHelperCases17.plan Lower6960.Prefix6969RescueData.HigherHelperCases17.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 7 1 1 900773 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases17.plan, Lower6960.Prefix6969MainCases.HigherHelperCases17.price, Lower6960.Prefix6969MainCases.HigherHelperCases17.valid, Lower6960.Prefix6969MainCases.HigherHelperCases17.priced, Lower6960.Prefix6969MainCases.HigherHelperCases17.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases17.plan, Lower6960.Prefix6969RescueData.HigherHelperCases17.price, Lower6960.Prefix6969RescueData.HigherHelperCases17.sources, Lower6960.Prefix6969RescueData.HigherHelperCases17.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 176138854959238191 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases17
end Z6969Source1685

-- Source: Research6969.PhysicalChecks116
section Z6969Source1686
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1768 : Request := ⟨⟨⟨556,772,170,6049⟩,5255817068544,9968090926⟩,10,8,2,1029454,3⟩
private theorem pass1768_2293 : (Triangular src1768) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1768_2294 : (Triangular src1768) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1768_2297 : (Triangular src1768) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1768_2306 : (Triangular src1768) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1768_2335 : (Triangular src1768) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1768 : Cover (Triangular src1768) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1768_2293, by decide, by decide, pass1768_2294, by decide, by decide, pass1768_2297, by decide, by decide, pass1768_2306, by decide, by decide, pass1768_2335, rfl⟩
def src1769 : Request := ⟨⟨⟨556,772,170,5951⟩,5255817068544,9968090926⟩,10,8,2,1029454,5⟩
private theorem pass1769_2293 : (Triangular src1769) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1769_2294 : (Triangular src1769) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1769_2297 : (Triangular src1769) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1769_2306 : (Triangular src1769) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1769_2335 : (Triangular src1769) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1769 : Cover (Triangular src1769) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1769_2293, by decide, by decide, pass1769_2294, by decide, by decide, pass1769_2297, by decide, by decide, pass1769_2306, by decide, by decide, pass1769_2335, rfl⟩
def src1770 : Request := ⟨⟨⟨556,772,170,5711⟩,5255817068544,9968090926⟩,10,8,2,1029454,10⟩
private theorem pass1770_2293 : (Triangular src1770) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1770_2294 : (Triangular src1770) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1770_2297 : (Triangular src1770) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1770_2306 : (Triangular src1770) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1770_2335 : (Triangular src1770) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1770 : Cover (Triangular src1770) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1770_2293, by decide, by decide, pass1770_2294, by decide, by decide, pass1770_2297, by decide, by decide, pass1770_2306, by decide, by decide, pass1770_2335, rfl⟩
def src1771 : Request := ⟨⟨⟨556,772,170,5392⟩,5255817068544,9968090926⟩,10,8,2,1029454,17⟩
private theorem pass1771_2293 : (Triangular src1771) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1771_2294 : (Triangular src1771) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1771_2297 : (Triangular src1771) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1771_2306 : (Triangular src1771) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1771_2335 : (Triangular src1771) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1771 : Cover (Triangular src1771) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1771_2293, by decide, by decide, pass1771_2294, by decide, by decide, pass1771_2297, by decide, by decide, pass1771_2306, by decide, by decide, pass1771_2335, rfl⟩
def src1772 : Request := ⟨⟨⟨556,772,170,4973⟩,5255817068544,9968090926⟩,10,8,2,1029454,27⟩
private theorem pass1772_2293 : (Triangular src1772) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1772_2294 : (Triangular src1772) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1772_2297 : (Triangular src1772) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1772_2306 : (Triangular src1772) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1772_2335 : (Triangular src1772) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1772 : Cover (Triangular src1772) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1772_2293, by decide, by decide, pass1772_2294, by decide, by decide, pass1772_2297, by decide, by decide, pass1772_2306, by decide, by decide, pass1772_2335, rfl⟩
def src1773 : Request := ⟨⟨⟨556,772,170,4445⟩,5255817068544,9968090926⟩,10,8,2,1029454,42⟩
private theorem pass1773_2293 : (Triangular src1773) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1773_2294 : (Triangular src1773) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1773_2297 : (Triangular src1773) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1773_2306 : (Triangular src1773) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1773_2335 : (Triangular src1773) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1773 : Cover (Triangular src1773) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1773_2293, by decide, by decide, pass1773_2294, by decide, by decide, pass1773_2297, by decide, by decide, pass1773_2306, by decide, by decide, pass1773_2335, rfl⟩
def src1862 : Request := ⟨⟨⟨1750,2442,527,84533⟩,161065121873920,975196209190⟩,0,2,1,257073,1⟩
private theorem pass1862_2390 : (Triangular src1862) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1862_2391 : (Triangular src1862) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1862_2393 : (Triangular src1862) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1862_2398 : (Triangular src1862) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1862_2412 : (Triangular src1862) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1862_2449 : (Triangular src1862) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1862 : Cover (Triangular src1862) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1862_2390, by decide, by decide, pass1862_2391, by decide, by decide, pass1862_2393, by decide, by decide, pass1862_2398, by decide, by decide, pass1862_2412, by decide, by decide, pass1862_2449, rfl⟩
def src1863 : Request := ⟨⟨⟨1750,2442,527,89172⟩,161065121873920,975196209190⟩,1,2,1,257073,1⟩
private theorem pass1863_2390 : (Triangular src1863) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1863_2391 : (Triangular src1863) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1863_2393 : (Triangular src1863) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1863_2398 : (Triangular src1863) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1863_2412 : (Triangular src1863) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1863_2449 : (Triangular src1863) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1863 : Cover (Triangular src1863) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1863_2390, by decide, by decide, pass1863_2391, by decide, by decide, pass1863_2393, by decide, by decide, pass1863_2398, by decide, by decide, pass1863_2412, by decide, by decide, pass1863_2449, rfl⟩
def src1864 : Request := ⟨⟨⟨1750,2442,527,94349⟩,161065121873920,975196209190⟩,2,2,1,257073,1⟩
private theorem pass1864_2390 : (Triangular src1864) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1864_2391 : (Triangular src1864) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1864_2393 : (Triangular src1864) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1864_2398 : (Triangular src1864) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1864_2412 : (Triangular src1864) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1864_2449 : (Triangular src1864) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1864 : Cover (Triangular src1864) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1864_2390, by decide, by decide, pass1864_2391, by decide, by decide, pass1864_2393, by decide, by decide, pass1864_2398, by decide, by decide, pass1864_2412, by decide, by decide, pass1864_2449, rfl⟩
def src1865 : Request := ⟨⟨⟨2100,2930,622,105447⟩,274699477319680,1994139134137⟩,3,2,1,257073,1⟩
private theorem pass1865_2390 : (Triangular src1865) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1865_2391 : (Triangular src1865) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1865_2393 : (Triangular src1865) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1865_2399 : (Triangular src1865) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1865_2415 : (Triangular src1865) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1865_2457 : (Triangular src1865) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1865 : Cover (Triangular src1865) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass1865_2390, by decide, by decide, pass1865_2391, by decide, by decide, pass1865_2393, by decide, by decide, pass1865_2399, by decide, by decide, pass1865_2415, by decide, by decide, pass1865_2457, rfl⟩
def src1866 : Request := ⟨⟨⟨2100,2930,632,110668⟩,278060332482560,2019119590628⟩,4,2,1,257073,1⟩
private theorem pass1866_2390 : (Triangular src1866) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1866_2391 : (Triangular src1866) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1866_2393 : (Triangular src1866) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1866_2398 : (Triangular src1866) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1866_2412 : (Triangular src1866) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1866_2449 : (Triangular src1866) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1866 : Cover (Triangular src1866) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1866_2390, by decide, by decide, pass1866_2391, by decide, by decide, pass1866_2393, by decide, by decide, pass1866_2398, by decide, by decide, pass1866_2412, by decide, by decide, pass1866_2449, rfl⟩
def src1867 : Request := ⟨⟨⟨2100,2930,632,122234⟩,278060332482560,2019119590628⟩,6,2,1,257073,1⟩
private theorem pass1867_2390 : (Triangular src1867) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1867_2391 : (Triangular src1867) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1867_2393 : (Triangular src1867) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1867_2398 : (Triangular src1867) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1867_2412 : (Triangular src1867) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1867_2449 : (Triangular src1867) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1867 : Cover (Triangular src1867) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1867_2390, by decide, by decide, pass1867_2391, by decide, by decide, pass1867_2393, by decide, by decide, pass1867_2398, by decide, by decide, pass1867_2412, by decide, by decide, pass1867_2449, rfl⟩
def src1868 : Request := ⟨⟨⟨2600,3628,783,152484⟩,527755772952576,4745819470168⟩,10,2,1,257073,1⟩
private theorem pass1868_2390 : (Triangular src1868) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1868_2391 : (Triangular src1868) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1868_2393 : (Triangular src1868) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1868_2398 : (Triangular src1868) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1868_2411 : (Triangular src1868) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1868_2446 : (Triangular src1868) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1868 : Cover (Triangular src1868) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1868_2390, by decide, by decide, pass1868_2391, by decide, by decide, pass1868_2393, by decide, by decide, pass1868_2398, by decide, by decide, pass1868_2411, by decide, by decide, pass1868_2446, rfl⟩
def src1869 : Request := ⟨⟨⟨3200,4465,963,161404⟩,983050615259136,10877088344236⟩,10,2,1,257073,1⟩
private theorem pass1869_2390 : (Triangular src1869) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1869_2391 : (Triangular src1869) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1869_2393 : (Triangular src1869) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1869_2398 : (Triangular src1869) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1869_2411 : (Triangular src1869) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1869_2445 : (Triangular src1869) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1869_2534 : (Triangular src1869) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1869 : Cover (Triangular src1869) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1869_2390, by decide, by decide, pass1869_2391, by decide, by decide, pass1869_2393, by decide, by decide, pass1869_2398, by decide, by decide, pass1869_2411, by decide, by decide, pass1869_2445, by decide, by decide, pass1869_2534, rfl⟩
def src1870 : Request := ⟨⟨⟨3200,4465,947,177211⟩,970564165959680,10735676910569⟩,13,2,1,257073,1⟩
private theorem pass1870_2390 : (Triangular src1870) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1870_2391 : (Triangular src1870) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1870_2393 : (Triangular src1870) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1870_2398 : (Triangular src1870) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1870_2412 : (Triangular src1870) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1870_2449 : (Triangular src1870) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1870 : Cover (Triangular src1870) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1870_2390, by decide, by decide, pass1870_2391, by decide, by decide, pass1870_2393, by decide, by decide, pass1870_2398, by decide, by decide, pass1870_2412, by decide, by decide, pass1870_2449, rfl⟩
def src1871 : Request := ⟨⟨⟨3950,5512,1189,191357⟩,1848744952463360,25255771038451⟩,13,2,1,257073,1⟩
private theorem pass1871_2390 : (Triangular src1871) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1871_2391 : (Triangular src1871) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1871_2393 : (Triangular src1871) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1871_2398 : (Triangular src1871) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1871_2411 : (Triangular src1871) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1871_2445 : (Triangular src1871) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1871_2534 : (Triangular src1871) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1871 : Cover (Triangular src1871) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1871_2390, by decide, by decide, pass1871_2391, by decide, by decide, pass1871_2393, by decide, by decide, pass1871_2398, by decide, by decide, pass1871_2411, by decide, by decide, pass1871_2445, by decide, by decide, pass1871_2534, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1686

-- Source: Research6969.PrefixMainDataHigherHelperCases18
section Z6969Source1687
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases18
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 65, 105, 75, 75] i
  bank i := ![bank3 1490, bank10 1603, bank19 1656, bank24 1838, bank28 2005, bank37 2039, bank42 2497, bank52 2900, bank65 3612, bank83 5597, bank83 2752, bank123 3616, bank122 24063, bank159 6076, bank199 9241, bank158 51722, bank230 14067, bank172 88577, bank171 201573] i
  head := src1768
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14995, 163891, 756134, 3637577],
    ![24861/2, 245137/2, 2235601/4, 2569609],
    ![6218, 529529/9, 2235601/4, 2504286],
    ![29433/8, 572567/16, 2592442/9, 11118062/9],
    ![62542/25, 619104/25, 411025/2, 4020025/4],
    ![17323/9, 655129/36, 2947231/16, 12333911/16],
    ![36739/32, 23473/2, 1203554/9, 15104353/25],
    ![86036/121, 874087/121, 564381/7, 17542100/49],
    ![86036/121, 874087/121, 564381/7, 17542100/49],
    ![254619/484, 2955506/441, 3339997/49, 17542100/49],
    ![254619/484, 2955506/441, 3339997/49, 8323424/25],
    ![254619/484, 691996/121, 60568, 204304],
    ![41249/100, 691996/121, 60568, 204304],
    ![41249/100, 418299/80, 48422, 188356],
    ![41249/100, 6226930/1323, 42071589/968, 167696427/968],
    ![480716/1323, 6226930/1323, 42071589/968, 167696427/968],
    ![480716/1323, 1398985/306, 35732375/864, 15757645/96],
    ![1872696/5329, 1398985/306, 35732375/864, 15757645/96],
    ![1826342/5329, 1398985/306, 35732375/864, 15757645/96]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 7 2 900773 := by
  refine ⟨?_, rank154 6049, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1768⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free19_0
    · exact free24_0
    · exact free28_0
    · exact free37_0
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free83_1
    · exact free83_0
    · exact free123_0
    · exact free122_0
    · exact free159_0
    · exact free199_0
    · exact free158_0
    · exact free230_0
    · exact free172_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [317909917, 317545660, 316822379, 316869119, 316271261, 317493267, 316333535, 154922504, 154901323, 154945124, 154574555, 69947002, 69984857, 83247552, 82666949, 124199456, 100665208, 139316473, 234156515], [1098701, 1100564, 1104264, 1104025, 1107084, 1100832, 1106765, 2485035, 2485387, 2484659, 2490820, 5730322, 5727313, 4789140, 4823616, 3146114, 3926577, 2784926, 1578460],
  ![124294961292300, 1606848132460, 211139075200, 5348393800], 174293999700704031⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 1398985/306, 35732375/864, 15757645/96] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases18
end Z6969Source1687

-- Source: Research6969.PhysicalChecks112
section Z6969Source1688
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1704 : Request := ⟨⟨⟨3950,5507,1244,81311⟩,1913299978158080,26084011577468⟩,145,7,1,900773,2⟩
private theorem pass1704_2293 : (Triangular src1704) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1704_2296 : (Triangular src1704) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1704_2304 : (Triangular src1704) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1704_2326 : (Triangular src1704) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1704_2387 : (Triangular src1704) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1704 : Cover (Triangular src1704) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass1704_2293, by decide, by decide, pass1704_2296, by decide, by decide, pass1704_2304, by decide, by decide, pass1704_2326, by decide, by decide, pass1704_2387, rfl⟩
def src1705 : Request := ⟨⟨⟨6900,9621,2174,130242⟩,10196763128627200,242895948111878⟩,245,7,1,900773,2⟩
private theorem pass1705_2293 : (Triangular src1705) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1705_2295 : (Triangular src1705) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1705_2301 : (Triangular src1705) 2301 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1705_2317 : (Triangular src1705) 2317 2360 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1705_2361 : (Triangular src1705) 2361 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1705 : Cover (Triangular src1705) 2389 2293 [2294,2300,2316,2360,2389] := by
  exact ⟨by decide, by decide, pass1705_2293, by decide, by decide, pass1705_2295, by decide, by decide, pass1705_2301, by decide, by decide, pass1705_2317, by decide, by decide, pass1705_2361, rfl⟩
def src1706 : Request := ⟨⟨⟨275,383,84,5419⟩,640970915840,608607683⟩,0,7,1,900773,4⟩
private theorem pass1706_2293 : (Triangular src1706) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1706_2306 : (Triangular src1706) 2306 2355 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1706_2356 : (Triangular src1706) 2356 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1706 : Cover (Triangular src1706) 2389 2293 [2305,2355,2389] := by
  exact ⟨by decide, by decide, pass1706_2293, by decide, by decide, pass1706_2306, by decide, by decide, pass1706_2356, rfl⟩
def src1707 : Request := ⟨⟨⟨325,453,98,6096⟩,1045036793856,1174588250⟩,1,7,1,900773,4⟩
private theorem pass1707_2293 : (Triangular src1707) 2293 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1707_2319 : (Triangular src1707) 2319 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1707 : Cover (Triangular src1707) 2389 2293 [2318,2389] := by
  exact ⟨by decide, by decide, pass1707_2293, by decide, by decide, pass1707_2319, rfl⟩
def src1708 : Request := ⟨⟨⟨325,453,98,6858⟩,1045036793856,1174588250⟩,2,7,1,900773,4⟩
private theorem pass1708_2293 : (Triangular src1708) 2293 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1708_2319 : (Triangular src1708) 2319 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1708 : Cover (Triangular src1708) 2389 2293 [2318,2389] := by
  exact ⟨by decide, by decide, pass1708_2293, by decide, by decide, pass1708_2319, rfl⟩
def src1709 : Request := ⟨⟨⟨325,453,98,8679⟩,1045036793856,1174588250⟩,4,7,1,900773,4⟩
private theorem pass1709_2293 : (Triangular src1709) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1709_2299 : (Triangular src1709) 2299 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1709_2320 : (Triangular src1709) 2320 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1709 : Cover (Triangular src1709) 2389 2293 [2298,2319,2389] := by
  exact ⟨by decide, by decide, pass1709_2293, by decide, by decide, pass1709_2299, by decide, by decide, pass1709_2320, rfl⟩
def src1710 : Request := ⟨⟨⟨470,655,144,9763⟩,3184589537280,5168862572⟩,8,7,1,900773,4⟩
private theorem pass1710_2293 : (Triangular src1710) 2293 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1710_2307 : (Triangular src1710) 2307 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1710_2353 : (Triangular src1710) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1710 : Cover (Triangular src1710) 2389 2293 [2306,2352,2389] := by
  exact ⟨by decide, by decide, pass1710_2293, by decide, by decide, pass1710_2307, by decide, by decide, pass1710_2353, rfl⟩
def src1711 : Request := ⟨⟨⟨825,1150,253,15636⟩,17161575202816,48873782027⟩,20,7,1,900773,4⟩
private theorem pass1711_2293 : (Triangular src1711) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1711_2306 : (Triangular src1711) 2306 2344 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1711_2345 : (Triangular src1711) 2345 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1711 : Cover (Triangular src1711) 2389 2293 [2305,2344,2389] := by
  exact ⟨by decide, by decide, pass1711_2293, by decide, by decide, pass1711_2306, by decide, by decide, pass1711_2345, rfl⟩
def src1712 : Request := ⟨⟨⟨825,1150,253,31694⟩,17161575202816,48873782027⟩,32,7,1,900773,4⟩
private theorem pass1712_2293 : (Triangular src1712) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1712_2294 : (Triangular src1712) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1712_2297 : (Triangular src1712) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1712_2306 : (Triangular src1712) 2306 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1712_2333 : (Triangular src1712) 2333 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1712 : Cover (Triangular src1712) 2389 2293 [2293,2296,2305,2332,2389] := by
  exact ⟨by decide, by decide, pass1712_2293, by decide, by decide, pass1712_2294, by decide, by decide, pass1712_2297, by decide, by decide, pass1712_2306, by decide, by decide, pass1712_2333, rfl⟩
def src1713 : Request := ⟨⟨⟨1450,2022,445,25043⟩,92998964346880,465769321795⟩,40,7,1,900773,4⟩
private theorem pass1713_2293 : (Triangular src1713) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1713_2296 : (Triangular src1713) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1713_2304 : (Triangular src1713) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1713_2327 : (Triangular src1713) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1713 : Cover (Triangular src1713) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass1713_2293, by decide, by decide, pass1713_2296, by decide, by decide, pass1713_2304, by decide, by decide, pass1713_2327, rfl⟩
def src1714 : Request := ⟨⟨⟨2600,3623,798,264035⟩,535425056505856,4795161706555⟩,145,7,1,900773,4⟩
private theorem pass1714_2293 : (Triangular src1714) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1714_2297 : (Triangular src1714) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1714_2308 : (Triangular src1714) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1714_2339 : (Triangular src1714) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1714 : Cover (Triangular src1714) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass1714_2293, by decide, by decide, pass1714_2297, by decide, by decide, pass1714_2308, by decide, by decide, pass1714_2339, rfl⟩
def src1715 : Request := ⟨⟨⟨3950,5507,1213,81311⟩,1877062482395136,25577387039299⟩,145,7,1,900773,4⟩
private theorem pass1715_2293 : (Triangular src1715) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1715_2302 : (Triangular src1715) 2302 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1715_2327 : (Triangular src1715) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1715 : Cover (Triangular src1715) 2389 2293 [2301,2326,2389] := by
  exact ⟨by decide, by decide, pass1715_2293, by decide, by decide, pass1715_2302, by decide, by decide, pass1715_2327, rfl⟩
def src1716 : Request := ⟨⟨⟨6900,9621,2118,130242⟩,9997036108906496,238016971510476⟩,245,7,1,900773,4⟩
private theorem pass1716_2293 : (Triangular src1716) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1716_2302 : (Triangular src1716) 2302 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1716_2327 : (Triangular src1716) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1716 : Cover (Triangular src1716) 2389 2293 [2301,2326,2389] := by
  exact ⟨by decide, by decide, pass1716_2293, by decide, by decide, pass1716_2302, by decide, by decide, pass1716_2327, rfl⟩
def src1717 : Request := ⟨⟨⟨325,453,100,4817⟩,1061047500800,1193036697⟩,0,7,1,900773,9⟩
private theorem pass1717_2293 : (Triangular src1717) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1717_2306 : (Triangular src1717) 2306 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1717_2352 : (Triangular src1717) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1717 : Cover (Triangular src1717) 2389 2293 [2305,2351,2389] := by
  exact ⟨by decide, by decide, pass1717_2293, by decide, by decide, pass1717_2306, by decide, by decide, pass1717_2352, rfl⟩
def src1718 : Request := ⟨⟨⟨325,453,98,5419⟩,1045036793856,1174588250⟩,1,7,1,900773,9⟩
private theorem pass1718_2293 : (Triangular src1718) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1718_2296 : (Triangular src1718) 2296 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1718_2307 : (Triangular src1718) 2307 2345 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1718_2346 : (Triangular src1718) 2346 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1718 : Cover (Triangular src1718) 2389 2293 [2295,2306,2345,2389] := by
  exact ⟨by decide, by decide, pass1718_2293, by decide, by decide, pass1718_2296, by decide, by decide, pass1718_2307, by decide, by decide, pass1718_2346, rfl⟩
def src1719 : Request := ⟨⟨⟨325,453,98,6858⟩,1045036793856,1174588250⟩,3,7,1,900773,9⟩
private theorem pass1719_2293 : (Triangular src1719) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1719_2295 : (Triangular src1719) 2295 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1719_2302 : (Triangular src1719) 2302 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1719_2327 : (Triangular src1719) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1719 : Cover (Triangular src1719) 2389 2293 [2294,2301,2326,2389] := by
  exact ⟨by decide, by decide, pass1719_2293, by decide, by decide, pass1719_2295, by decide, by decide, pass1719_2302, by decide, by decide, pass1719_2327, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1688

-- Source: Research6969.PrefixRescueDataHigherHelperCases18
section Z6969Source1689
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases18
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,7,1,3⟩
  bank i := ![bank101 5419, bank100 6096, bank100 7715, bank143 9763, bank192 12355, bank202 15636, bank240 31694, bank239 91474, bank307 81311, bank350 130242] i
  reserve i := ![0, 1, 3, 8, 13, 20, 50, 85, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900773
  seedFloor := 2

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 5419
    · exact rank100 6096
    · exact rank100 7715
    · exact rank143 9763
    · exact rank192 12355
    · exact rank202 15636
    · exact rank240 31694
    · exact rank239 91474
    · exact rank307 81311
    · exact rank350 130242
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1696⟩
    · exact ⟨_, cover1697⟩
    · exact ⟨_, cover1698⟩
    · exact ⟨_, cover1699⟩
    · exact ⟨_, cover1700⟩
    · exact ⟨_, cover1701⟩
    · exact ⟨_, cover1702⟩
    · exact ⟨_, cover1703⟩
    · exact ⟨_, cover1704⟩
    · exact ⟨_, cover1705⟩

def price : EarlyPrice := ⟨7, 3, 9, 95/100, 80/100, ![152107417686, 312911799589, 2538977642, 5077950936], 483642867608833⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5661/86, 22794/41, 313519/82, 65121/41] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases18
end Z6969Source1689

-- Source: Research6969.PrefixNearSavedHigherHelperCases18
section Z6969Source1690
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases18
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4571,65,555,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases18.plan Lower6960.Prefix6969RescueData.HigherHelperCases18.plan Lower6960.Prefix6969RescueData.HigherHelperCases18.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 7 2 3 900773 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases18.plan, Lower6960.Prefix6969MainCases.HigherHelperCases18.price, Lower6960.Prefix6969MainCases.HigherHelperCases18.valid, Lower6960.Prefix6969MainCases.HigherHelperCases18.priced, Lower6960.Prefix6969MainCases.HigherHelperCases18.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases18.plan, Lower6960.Prefix6969RescueData.HigherHelperCases18.price, Lower6960.Prefix6969RescueData.HigherHelperCases18.sources, Lower6960.Prefix6969RescueData.HigherHelperCases18.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 177710714298050484 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases18
end Z6969Source1690

-- Source: Research6969.PrefixMainDataHigherHelperCases19
section Z6969Source1691
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases19
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 65, 105, 75] i
  bank i := ![bank3 1490, bank10 1603, bank19 1656, bank24 1838, bank28 2005, bank37 2039, bank42 2497, bank52 2900, bank65 3612, bank83 5597, bank83 2752, bank123 3616, bank122 24063, bank159 6076, bank199 9241, bank158 51722, bank230 14067, bank171 201573] i
  head := src1769
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14995, 163597, 754468, 3621505],
    ![24861/2, 243373/2, 2219431/4, 2569609],
    ![6218, 525511/9, 2219431/4, 2463714],
    ![29433/8, 568353/16, 857810/3, 10937938/9],
    ![62542/25, 614596/25, 411025/2, 4020025/4],
    ![17323/9, 650131/36, 2924985/16, 12134089/16],
    ![36739/32, 186461/16, 1203554/9, 14859647/25],
    ![86036/121, 867913/121, 560419/7, 17257900/49],
    ![86036/121, 867913/121, 560419/7, 17257900/49],
    ![254619/484, 2938454/441, 3320887/49, 17257900/49],
    ![254619/484, 2938454/441, 3320887/49, 8188576/25],
    ![254619/484, 686116/121, 60568, 204304],
    ![41249/100, 686116/121, 60568, 204304],
    ![41249/100, 414869/80, 48422, 188356],
    ![41249/100, 6176950/1323, 41736723/968, 14998143/88],
    ![480716/1323, 6176950/1323, 41736723/968, 14998143/88],
    ![480716/1323, 1387715/306, 35446705/864, 197880489/1225],
    ![1826342/5329, 1387715/306, 35446705/864, 197880489/1225]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 7 4 900773 := by
  refine ⟨?_, rank154 5951, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1769⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free19_0
    · exact free24_0
    · exact free28_0
    · exact free37_0
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free83_1
    · exact free83_0
    · exact free123_0
    · exact free122_0
    · exact free159_0
    · exact free199_0
    · exact free158_0
    · exact free230_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [315980199, 315520695, 315559081, 315472880, 315329532, 314654369, 314515481, 147162387, 147055704, 147087099, 147071052, 69753772, 69847566, 82850144, 82177641, 123027857, 141173983, 233737993], [1108573, 1110923, 1110727, 1111168, 1111901, 1115355, 1116066, 2614057, 2615831, 2615309, 2615575, 5746855, 5738355, 4812738, 4852671, 3178865, 2744201, 1581901],
  ![124072801444260, 1607300257832, 210364193700, 5404070500], 173346997905973677⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 16 _
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

theorem final_cap : plan.history plan.last = ![1826342/5329, 1387715/306, 35446705/864, 197880489/1225] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases19
end Z6969Source1691

end Merged_Z6969Pack0718

-- merged module Z6969Pack0719
section Merged_Z6969Pack0719

-- Source: Research6969.PrefixRescueDataHigherHelperCases19
section Z6969Source1692
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases19
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,8⟩
  bank i := ![bank79 5419, bank100 6096, bank100 6858, bank100 8679, bank142 9763, bank201 15636, bank201 31694, bank233 25043, bank306 81311, bank258 264035, bank349 130242] i
  reserve i := ![0, 1, 2, 4, 8, 20, 32, 40, 145, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900773
  seedFloor := 4

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank79 5419
    · exact rank100 6096
    · exact rank100 6858
    · exact rank100 8679
    · exact rank142 9763
    · exact rank201 15636
    · exact rank201 31694
    · exact rank233 25043
    · exact rank306 81311
    · exact rank258 264035
    · exact rank349 130242
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1706⟩
    · exact ⟨_, cover1707⟩
    · exact ⟨_, cover1708⟩
    · exact ⟨_, cover1709⟩
    · exact ⟨_, cover1710⟩
    · exact ⟨_, cover1711⟩
    · exact ⟨_, cover1712⟩
    · exact ⟨_, cover1713⟩
    · exact ⟨_, cover1715⟩
    · exact ⟨_, cover1714⟩
    · exact ⟨_, cover1716⟩

def price : EarlyPrice := ⟨7, 8, 10, 90/100, 80/100, ![822296346110, 625521475190, 6596184828, 4947148152], 820725997852544⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8411/146, 24531/41, 164777/41, 173656/41] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases19
end Z6969Source1692

-- Source: Research6969.PrefixNearSavedHigherHelperCases19
section Z6969Source1693
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases19
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4535,57,598,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases19.plan Lower6960.Prefix6969RescueData.HigherHelperCases19.plan Lower6960.Prefix6969RescueData.HigherHelperCases19.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 7 4 8 900773 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases19.plan, Lower6960.Prefix6969MainCases.HigherHelperCases19.price, Lower6960.Prefix6969MainCases.HigherHelperCases19.valid, Lower6960.Prefix6969MainCases.HigherHelperCases19.priced, Lower6960.Prefix6969MainCases.HigherHelperCases19.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases19.plan, Lower6960.Prefix6969RescueData.HigherHelperCases19.price, Lower6960.Prefix6969RescueData.HigherHelperCases19.sources, Lower6960.Prefix6969RescueData.HigherHelperCases19.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 182999797992705567 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases19
end Z6969Source1693

-- Source: Research6969.PrefixMainDataHigherHelperCases20
section Z6969Source1694
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases20
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 75, 105, 75, 75] i
  bank i := ![bank3 1490, bank10 1603, bank19 1656, bank24 1838, bank33 1882, bank37 2039, bank42 2497, bank52 2900, bank65 3612, bank83 5597, bank83 2752, bank123 3616, bank124 22589, bank159 6076, bank199 9241, bank187 32183, bank230 14067, bank172 88577, bank171 201573] i
  head := src1770
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15024, 162795, 750204, 3571086],
    ![24861/2, 239053/2, 2179831/4, 2569609],
    ![6218, 515671/9, 2179831/4, 2364354],
    ![29433/8, 558033/16, 842290/3, 10496818/9],
    ![65616/25, 594068/25, 203256, 885481],
    ![17323/9, 637891/36, 2870505/16, 11644729/16],
    ![36739/32, 183221/16, 660807/5, 14260367/25],
    ![86036/121, 852793/121, 3855013/49, 16561900/49],
    ![86036/121, 852793/121, 3855013/49, 16561900/49],
    ![254619/484, 2896694/441, 3274087/49, 16561900/49],
    ![254619/484, 2896694/441, 3274087/49, 7858336/25],
    ![254619/484, 671716/121, 2926324/49, 204304],
    ![20667/50, 671716/121, 2926324/49, 204304],
    ![20667/50, 406469/80, 48422, 188356],
    ![20667/50, 6054550/1323, 40916643/968, 158326053/968],
    ![1960504/5329, 6054550/1323, 40916643/968, 158326053/968],
    ![1960504/5329, 1360115/306, 34747105/864, 803366370/5041],
    ![1872696/5329, 1360115/306, 34747105/864, 803366370/5041],
    ![1826342/5329, 1360115/306, 34747105/864, 803366370/5041]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 7 9 900773 := by
  refine ⟨?_, rank154 5711, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1770⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free19_0
    · exact free24_0
    · exact free33_0
    · exact free37_0
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free83_1
    · exact free83_0
    · exact free123_0
    · exact free124_0
    · exact free159_0
    · exact free199_0
    · exact free187_0
    · exact free230_0
    · exact free172_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [311339334, 310450673, 311054673, 311326176, 311029889, 311279506, 310729566, 145484831, 145516678, 145802952, 145648733, 69979938, 69998712, 81906024, 87879174, 122892878, 99175070, 137424158, 232713039], [1132314, 1136861, 1133771, 1132382, 1133897, 1132620, 1135434, 2649686, 2648988, 2642712, 2646093, 5727704, 5726212, 4868800, 4522277, 3182638, 3989468, 2826415, 1590328],
  ![123528735361980, 1608407529036, 209441735100, 5410484600], 170266236078756023⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 1360115/306, 34747105/864, 803366370/5041] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases20
end Z6969Source1694

-- Source: Research6969.PhysicalChecks113
section Z6969Source1695
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1720 : Request := ⟨⟨⟨470,655,148,8679⟩,3250957582336,5279398867⟩,8,7,1,900773,9⟩
private theorem pass1720_2293 : (Triangular src1720) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1720_2296 : (Triangular src1720) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1720_2305 : (Triangular src1720) 2305 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1720_2335 : (Triangular src1720) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1720 : Cover (Triangular src1720) 2389 2293 [2295,2304,2334,2389] := by
  exact ⟨by decide, by decide, pass1720_2293, by decide, by decide, pass1720_2296, by decide, by decide, pass1720_2305, by decide, by decide, pass1720_2335, rfl⟩
def src1721 : Request := ⟨⟨⟨825,1150,260,13899⟩,17518948515840,49918096074⟩,20,7,1,900773,9⟩
private theorem pass1721_2293 : (Triangular src1721) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1721_2295 : (Triangular src1721) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1721_2301 : (Triangular src1721) 2301 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1721_2319 : (Triangular src1721) 2319 2372 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1721_2373 : (Triangular src1721) 2373 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1721 : Cover (Triangular src1721) 2389 2293 [2294,2300,2318,2372,2389] := by
  exact ⟨by decide, by decide, pass1721_2293, by decide, by decide, pass1721_2295, by decide, by decide, pass1721_2301, by decide, by decide, pass1721_2319, by decide, by decide, pass1721_2373, rfl⟩
def src1722 : Request := ⟨⟨⟨1000,1393,307,102908⟩,30557599170560,105228376929⟩,50,7,1,900773,9⟩
private theorem pass1722_2293 : (Triangular src1722) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1722_2294 : (Triangular src1722) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1722_2297 : (Triangular src1722) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1722_2306 : (Triangular src1722) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1722_2332 : (Triangular src1722) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1722 : Cover (Triangular src1722) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass1722_2293, by decide, by decide, pass1722_2294, by decide, by decide, pass1722_2297, by decide, by decide, pass1722_2306, by decide, by decide, pass1722_2332, rfl⟩
def src1723 : Request := ⟨⟨⟨2100,2928,645,35655⟩,282396798484480,2046887686018⟩,65,7,1,900773,9⟩
private theorem pass1723_2293 : (Triangular src1723) 2293 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1723_2309 : (Triangular src1723) 2309 2354 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1723_2355 : (Triangular src1723) 2355 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1723 : Cover (Triangular src1723) 2389 2293 [2308,2354,2389] := by
  exact ⟨by decide, by decide, pass1723_2293, by decide, by decide, pass1723_2309, by decide, by decide, pass1723_2355, rfl⟩
def src1724 : Request := ⟨⟨⟨3200,4459,1008,602179⟩,1017717693874176,11221829825062⟩,190,7,1,900773,9⟩
private theorem pass1724_2293 : (Triangular src1724) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1724_2299 : (Triangular src1724) 2299 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1724_2315 : (Triangular src1724) 2315 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1724_2360 : (Triangular src1724) 2360 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1724 : Cover (Triangular src1724) 2389 2293 [2298,2314,2359,2389] := by
  exact ⟨by decide, by decide, pass1724_2293, by decide, by decide, pass1724_2299, by decide, by decide, pass1724_2315, by decide, by decide, pass1724_2360, rfl⟩
def src1725 : Request := ⟨⟨⟨5700,7948,1750,91474⟩,5637370734182400,110890906752819⟩,190,7,1,900773,9⟩
private theorem pass1725_2293 : (Triangular src1725) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1725_2294 : (Triangular src1725) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1725_2297 : (Triangular src1725) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1725_2305 : (Triangular src1725) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1725_2327 : (Triangular src1725) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1725_2388 : (Triangular src1725) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1725 : Cover (Triangular src1725) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass1725_2293, by decide, by decide, pass1725_2294, by decide, by decide, pass1725_2297, by decide, by decide, pass1725_2305, by decide, by decide, pass1725_2327, by decide, by decide, pass1725_2388, rfl⟩
def src1726 : Request := ⟨⟨⟨3950,5504,1244,2474877⟩,1913299978158080,26038250013848⟩,245,7,1,900773,9⟩
private theorem pass1726_2293 : (Triangular src1726) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1726_2294 : (Triangular src1726) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1726_2297 : (Triangular src1726) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1726_2306 : (Triangular src1726) 2306 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1726_2330 : (Triangular src1726) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1726 : Cover (Triangular src1726) 2389 2293 [2293,2296,2305,2329,2389] := by
  exact ⟨by decide, by decide, pass1726_2293, by decide, by decide, pass1726_2294, by decide, by decide, pass1726_2297, by decide, by decide, pass1726_2306, by decide, by decide, pass1726_2330, rfl⟩
def src1727 : Request := ⟨⟨⟨325,453,100,4282⟩,1061047500800,1193036697⟩,0,7,1,900773,16⟩
private theorem pass1727_2293 : (Triangular src1727) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1727_2306 : (Triangular src1727) 2306 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1727_2353 : (Triangular src1727) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1727 : Cover (Triangular src1727) 2389 2293 [2305,2352,2389] := by
  exact ⟨by decide, by decide, pass1727_2293, by decide, by decide, pass1727_2306, by decide, by decide, pass1727_2353, rfl⟩
def src1728 : Request := ⟨⟨⟨325,453,98,4817⟩,1045036793856,1174588250⟩,1,7,1,900773,16⟩
private theorem pass1728_2293 : (Triangular src1728) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1728_2297 : (Triangular src1728) 2297 2310 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1728_2311 : (Triangular src1728) 2311 2360 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1728_2361 : (Triangular src1728) 2361 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1728 : Cover (Triangular src1728) 2389 2293 [2296,2310,2360,2389] := by
  exact ⟨by decide, by decide, pass1728_2293, by decide, by decide, pass1728_2297, by decide, by decide, pass1728_2311, by decide, by decide, pass1728_2361, rfl⟩
def src1729 : Request := ⟨⟨⟨325,453,98,5419⟩,1045036793856,1174588250⟩,2,7,1,900773,16⟩
private theorem pass1729_2293 : (Triangular src1729) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1729_2300 : (Triangular src1729) 2300 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1729_2326 : (Triangular src1729) 2326 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1729 : Cover (Triangular src1729) 2389 2293 [2299,2325,2389] := by
  exact ⟨by decide, by decide, pass1729_2293, by decide, by decide, pass1729_2300, by decide, by decide, pass1729_2326, rfl⟩
def src1730 : Request := ⟨⟨⟨400,558,123,6096⟩,1971918995456,2734096379⟩,4,7,1,900773,16⟩
private theorem pass1730_2293 : (Triangular src1730) 2293 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1730_2313 : (Triangular src1730) 2313 2380 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1730_2381 : (Triangular src1730) 2381 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1730 : Cover (Triangular src1730) 2389 2293 [2312,2380,2389] := by
  exact ⟨by decide, by decide, pass1730_2293, by decide, by decide, pass1730_2313, by decide, by decide, pass1730_2381, rfl⟩
def src1731 : Request := ⟨⟨⟨470,655,148,7715⟩,3250957582336,5279398867⟩,8,7,1,900773,16⟩
private theorem pass1731_2293 : (Triangular src1731) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1731_2298 : (Triangular src1731) 2298 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1731_2314 : (Triangular src1731) 2314 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1731_2366 : (Triangular src1731) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1731 : Cover (Triangular src1731) 2389 2293 [2297,2313,2365,2389] := by
  exact ⟨by decide, by decide, pass1731_2293, by decide, by decide, pass1731_2298, by decide, by decide, pass1731_2314, by decide, by decide, pass1731_2366, rfl⟩
def src1732 : Request := ⟨⟨⟨690,962,212,10983⟩,10065769922560,23997864317⟩,16,7,1,900773,16⟩
private theorem pass1732_2293 : (Triangular src1732) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1732_2294 : (Triangular src1732) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1732_2297 : (Triangular src1732) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1732_2306 : (Triangular src1732) 2306 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1732_2334 : (Triangular src1732) 2334 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1732 : Cover (Triangular src1732) 2389 2293 [2293,2296,2305,2333,2389] := by
  exact ⟨by decide, by decide, pass1732_2293, by decide, by decide, pass1732_2294, by decide, by decide, pass1732_2297, by decide, by decide, pass1732_2306, by decide, by decide, pass1732_2334, rfl⟩
def src1733 : Request := ⟨⟨⟨1200,1673,368,22261⟩,52718727069696,218387554859⟩,40,7,1,900773,16⟩
private theorem pass1733_2293 : (Triangular src1733) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1733_2295 : (Triangular src1733) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1733_2301 : (Triangular src1733) 2301 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1733_2319 : (Triangular src1733) 2319 2370 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1733_2371 : (Triangular src1733) 2371 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1733 : Cover (Triangular src1733) 2389 2293 [2294,2300,2318,2370,2389] := by
  exact ⟨by decide, by decide, pass1733_2293, by decide, by decide, pass1733_2295, by decide, by decide, pass1733_2301, by decide, by decide, pass1733_2319, by decide, by decide, pass1733_2371, rfl⟩
def src1734 : Request := ⟨⟨⟨1750,2439,537,72277⟩,163381988556800,985665319192⟩,85,7,1,900773,16⟩
private theorem pass1734_2293 : (Triangular src1734) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1734_2299 : (Triangular src1734) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1734_2316 : (Triangular src1734) 2316 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1734_2365 : (Triangular src1734) 2365 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1734 : Cover (Triangular src1734) 2389 2293 [2298,2315,2364,2389] := by
  exact ⟨by decide, by decide, pass1734_2293, by decide, by decide, pass1734_2299, by decide, by decide, pass1734_2316, by decide, by decide, pass1734_2365, rfl⟩
def src1735 : Request := ⟨⟨⟨3950,5507,1244,64247⟩,1913299978158080,26084011577468⟩,145,7,1,900773,16⟩
private theorem pass1735_2293 : (Triangular src1735) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1735_2296 : (Triangular src1735) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1735_2304 : (Triangular src1735) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1735_2326 : (Triangular src1735) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1735_2387 : (Triangular src1735) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1735 : Cover (Triangular src1735) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass1735_2293, by decide, by decide, pass1735_2296, by decide, by decide, pass1735_2304, by decide, by decide, pass1735_2326, by decide, by decide, pass1735_2387, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1695

-- Source: Research6969.PrefixRescueDataHigherHelperCases20
section Z6969Source1696
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases20
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,7,1,15⟩
  bank i := ![bank101 4817, bank100 5419, bank100 6858, bank143 8679, bank202 13899, bank247 35655, bank217 102908, bank336 91474, bank294 602179, bank305 2474877] i
  reserve i := ![0, 1, 3, 8, 20, 65, 50, 190, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900773
  seedFloor := 9

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 4817
    · exact rank100 5419
    · exact rank100 6858
    · exact rank143 8679
    · exact rank202 13899
    · exact rank247 35655
    · exact rank217 102908
    · exact rank336 91474
    · exact rank294 602179
    · exact rank305 2474877
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1717⟩
    · exact ⟨_, cover1718⟩
    · exact ⟨_, cover1719⟩
    · exact ⟨_, cover1720⟩
    · exact ⟨_, cover1721⟩
    · exact ⟨_, cover1723⟩
    · exact ⟨_, cover1722⟩
    · exact ⟨_, cover1725⟩
    · exact ⟨_, cover1724⟩
    · exact ⟨_, cover1726⟩

def price : EarlyPrice := ⟨7, 15, 9, 85/100, 70/100, ![14451786854292, 5805604427988, 10218943000, 4087587000], 4858856777334870⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![6484/123, 117724/191, 759538/191, 1372110/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases20
end Z6969Source1696

-- Source: Research6969.PrefixNearSavedHigherHelperCases20
section Z6969Source1697
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases20
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4444,52,616,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases20.plan Lower6960.Prefix6969RescueData.HigherHelperCases20.plan Lower6960.Prefix6969RescueData.HigherHelperCases20.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 7 9 15 900773 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases20.plan, Lower6960.Prefix6969MainCases.HigherHelperCases20.price, Lower6960.Prefix6969MainCases.HigherHelperCases20.valid, Lower6960.Prefix6969MainCases.HigherHelperCases20.priced, Lower6960.Prefix6969MainCases.HigherHelperCases20.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases20.plan, Lower6960.Prefix6969RescueData.HigherHelperCases20.price, Lower6960.Prefix6969RescueData.HigherHelperCases20.sources, Lower6960.Prefix6969RescueData.HigherHelperCases20.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 189374275566483741 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases20
end Z6969Source1697

-- Source: Research6969.PrefixMainDataHigherHelperCases21
section Z6969Source1698
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases21
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 13, 15, 21, 21, 30, 40, 40, 65, 75, 75, 75, 75] i
  bank i := ![bank3 1490, bank10 1603, bank19 1656, bank24 1838, bank33 1882, bank42 2171, bank55 2427, bank72 2841, bank65 3612, bank123 3616, bank89 4866, bank168 4492, bank124 22589, bank147 6388, bank199 9241, bank211 10626, bank187 32183, bank172 88577, bank171 201573] i
  head := src1771
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15815, 161551, 743070, 3314505],
    ![24861/2, 233311/2, 531799, 2569609],
    ![6218, 502592/9, 531799, 2232288],
    ![29433/8, 136079/4, 2464984/9, 9910496/9],
    ![65616/25, 578756/25, 203256, 885481],
    ![73478/49, 660238/49, 2975484/25, 4713241/9],
    ![45497/50, 386927/50, 361623/4, 1090532/3],
    ![45497/50, 386927/50, 2096658/25, 8071281/25],
    ![13307/16, 386927/50, 9351328/121, 8071281/25],
    ![84176/121, 652576/121, 2840832/49, 9748736/49],
    ![66774/121, 652576/121, 2840832/49, 9748736/49],
    ![66774/121, 652576/121, 2840832/49, 20178064/121],
    ![20667/50, 652576/121, 2840832/49, 20178064/121],
    ![20667/50, 247629/50, 2363560/49, 20178064/121],
    ![20667/50, 5891860/1323, 9956655/242, 85396081/529],
    ![20667/50, 23364236/5329, 364168/9, 100266936/625],
    ![1960504/5329, 23364236/5329, 364168/9, 100266936/625],
    ![1872696/5329, 23364236/5329, 364168/9, 100266936/625],
    ![1826342/5329, 23364236/5329, 364168/9, 100266936/625]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 7 16 900773 := by
  refine ⟨?_, rank154 5392, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1771⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free19_0
    · exact free24_0
    · exact free33_0
    · exact free42_0
    · exact free55_0
    · exact free72_0
    · exact free65_0
    · exact free123_0
    · exact free89_1
    · exact free168_0
    · exact free124_0
    · exact free147_0
    · exact free199_0
    · exact free211_0
    · exact free187_0
    · exact free172_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [308850082, 308003674, 307513234, 308609987, 308814805, 308803959, 147057977, 147136234, 147113516, 71548375, 102929134, 64876361, 61325510, 80461732, 93577248, 93965627, 99213676, 137462764, 232736375], [1145049, 1149379, 1151888, 1146277, 1145229, 1145285, 2615793, 2614492, 2614869, 5603049, 3831027, 6196978, 6566407, 4954561, 4234941, 4215356, 3987839, 2825568, 1590136],
  ![123541122577500, 1608382247020, 209462737500, 5053652220], 167925961315505702⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
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

theorem final_cap : plan.history plan.last = ![1826342/5329, 23364236/5329, 364168/9, 100266936/625] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases21
end Z6969Source1698

-- Source: Research6969.PhysicalChecks114
section Z6969Source1699
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1736 : Request := ⟨⟨⟨3200,4459,1008,475797⟩,1017717693874176,11221829825062⟩,190,7,1,900773,16⟩
private theorem pass1736_2293 : (Triangular src1736) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1736_2294 : (Triangular src1736) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1736_2297 : (Triangular src1736) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1736_2305 : (Triangular src1736) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1736_2327 : (Triangular src1736) 2327 2388 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1736_2389 : (Triangular src1736) 2389 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1736 : Cover (Triangular src1736) 2389 2293 [2293,2296,2304,2326,2388,2389] := by
  exact ⟨by decide, by decide, pass1736_2293, by decide, by decide, pass1736_2294, by decide, by decide, pass1736_2297, by decide, by decide, pass1736_2305, by decide, by decide, pass1736_2327, by decide, by decide, pass1736_2389, rfl⟩
def src1737 : Request := ⟨⟨⟨6900,9621,2174,102908⟩,10196763128627200,242895948111878⟩,245,7,1,900773,16⟩
private theorem pass1737_2293 : (Triangular src1737) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1737_2295 : (Triangular src1737) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1737_2300 : (Triangular src1737) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1737_2314 : (Triangular src1737) 2314 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1737_2352 : (Triangular src1737) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1737 : Cover (Triangular src1737) 2389 2293 [2294,2299,2313,2351,2389] := by
  exact ⟨by decide, by decide, pass1737_2293, by decide, by decide, pass1737_2295, by decide, by decide, pass1737_2300, by decide, by decide, pass1737_2314, by decide, by decide, pass1737_2352, rfl⟩
def src1738 : Request := ⟨⟨⟨225,314,69,4282⟩,353440890880,276676118⟩,0,7,1,900773,26⟩
private theorem pass1738_2293 : (Triangular src1738) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1738_2299 : (Triangular src1738) 2299 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1738_2323 : (Triangular src1738) 2323 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1738 : Cover (Triangular src1738) 2389 2293 [2298,2322,2389] := by
  exact ⟨by decide, by decide, pass1738_2293, by decide, by decide, pass1738_2299, by decide, by decide, pass1738_2323, rfl⟩
def src1739 : Request := ⟨⟨⟨275,383,83,4282⟩,635228389376,603020643⟩,1,7,1,900773,26⟩
private theorem pass1739_2293 : (Triangular src1739) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1739_2296 : (Triangular src1739) 2296 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1739_2308 : (Triangular src1739) 2308 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1739_2353 : (Triangular src1739) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1739 : Cover (Triangular src1739) 2389 2293 [2295,2307,2352,2389] := by
  exact ⟨by decide, by decide, pass1739_2293, by decide, by decide, pass1739_2296, by decide, by decide, pass1739_2308, by decide, by decide, pass1739_2353, rfl⟩
def src1740 : Request := ⟨⟨⟨325,453,100,4817⟩,1061047500800,1193036697⟩,3,7,1,900773,26⟩
private theorem pass1740_2293 : (Triangular src1740) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1740_2294 : (Triangular src1740) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1740_2297 : (Triangular src1740) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1740_2308 : (Triangular src1740) 2308 2346 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1740_2347 : (Triangular src1740) 2347 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1740 : Cover (Triangular src1740) 2389 2293 [2293,2296,2307,2346,2389] := by
  exact ⟨by decide, by decide, pass1740_2293, by decide, by decide, pass1740_2294, by decide, by decide, pass1740_2297, by decide, by decide, pass1740_2308, by decide, by decide, pass1740_2347, rfl⟩
def src1741 : Request := ⟨⟨⟨400,558,123,6096⟩,1971918995456,2734096379⟩,6,7,1,900773,26⟩
private theorem pass1741_2293 : (Triangular src1741) 2293 2309 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1741_2310 : (Triangular src1741) 2310 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1741_2368 : (Triangular src1741) 2368 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1741 : Cover (Triangular src1741) 2389 2293 [2309,2367,2389] := by
  exact ⟨by decide, by decide, pass1741_2293, by decide, by decide, pass1741_2310, by decide, by decide, pass1741_2368, rfl⟩
def src1742 : Request := ⟨⟨⟨560,781,172,8679⟩,5388141854720,10440670587⟩,13,7,1,900773,26⟩
private theorem pass1742_2293 : (Triangular src1742) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1742_2302 : (Triangular src1742) 2302 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1742_2331 : (Triangular src1742) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1742 : Cover (Triangular src1742) 2389 2293 [2301,2330,2389] := by
  exact ⟨by decide, by decide, pass1742_2293, by decide, by decide, pass1742_2302, by decide, by decide, pass1742_2331, rfl⟩
def src1743 : Request := ⟨⟨⟨1000,1394,307,15636⟩,30557599170560,105471636407⟩,32,7,1,900773,26⟩
private theorem pass1743_2293 : (Triangular src1743) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1743_2296 : (Triangular src1743) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1743_2305 : (Triangular src1743) 2305 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1743_2332 : (Triangular src1743) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1743 : Cover (Triangular src1743) 2389 2293 [2295,2304,2331,2389] := by
  exact ⟨by decide, by decide, pass1743_2293, by decide, by decide, pass1743_2296, by decide, by decide, pass1743_2305, by decide, by decide, pass1743_2332, rfl⟩
def src1744 : Request := ⟨⟨⟨2600,3624,798,50764⟩,535425056505856,4799424311630⟩,110,7,1,900773,26⟩
private theorem pass1744_2293 : (Triangular src1744) 2293 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1744_2309 : (Triangular src1744) 2309 2353 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1744_2354 : (Triangular src1744) 2354 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1744 : Cover (Triangular src1744) 2389 2293 [2308,2353,2389] := by
  exact ⟨by decide, by decide, pass1744_2293, by decide, by decide, pass1744_2309, by decide, by decide, pass1744_2354, rfl⟩
def src1745 : Request := ⟨⟨⟨2600,3623,819,164837⟩,546063062138880,4892906717079⟩,145,7,1,900773,26⟩
private theorem pass1745_2293 : (Triangular src1745) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1745_2300 : (Triangular src1745) 2300 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1745_2319 : (Triangular src1745) 2319 2372 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1745_2373 : (Triangular src1745) 2373 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1745 : Cover (Triangular src1745) 2389 2293 [2299,2318,2372,2389] := by
  exact ⟨by decide, by decide, pass1745_2293, by decide, by decide, pass1745_2300, by decide, by decide, pass1745_2319, by decide, by decide, pass1745_2373, rfl⟩
def src1746 : Request := ⟨⟨⟨3200,4459,1008,422931⟩,1017717693874176,11221829825062⟩,190,7,1,900773,26⟩
private theorem pass1746_2293 : (Triangular src1746) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1746_2299 : (Triangular src1746) 2299 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1746_2315 : (Triangular src1746) 2315 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1746_2360 : (Triangular src1746) 2360 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1746 : Cover (Triangular src1746) 2389 2293 [2298,2314,2359,2389] := by
  exact ⟨by decide, by decide, pass1746_2293, by decide, by decide, pass1746_2299, by decide, by decide, pass1746_2315, by decide, by decide, pass1746_2360, rfl⟩
def src1747 : Request := ⟨⟨⟨4800,6692,1512,72277⟩,3433136573644800,56871238465897⟩,190,7,1,900773,26⟩
private theorem pass1747_2293 : (Triangular src1747) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1747_2302 : (Triangular src1747) 2302 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1747_2327 : (Triangular src1747) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1747 : Cover (Triangular src1747) 2389 2293 [2301,2326,2389] := by
  exact ⟨by decide, by decide, pass1747_2293, by decide, by decide, pass1747_2302, by decide, by decide, pass1747_2327, rfl⟩
def src1748 : Request := ⟨⟨⟨3950,5504,1244,1738186⟩,1913299978158080,26038250013848⟩,245,7,1,900773,26⟩
private theorem pass1748_2293 : (Triangular src1748) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1748_2294 : (Triangular src1748) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1748_2297 : (Triangular src1748) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1748_2306 : (Triangular src1748) 2306 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1748_2330 : (Triangular src1748) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1748 : Cover (Triangular src1748) 2389 2293 [2293,2296,2305,2329,2389] := by
  exact ⟨by decide, by decide, pass1748_2293, by decide, by decide, pass1748_2294, by decide, by decide, pass1748_2297, by decide, by decide, pass1748_2306, by decide, by decide, pass1748_2330, rfl⟩
def src1749 : Request := ⟨⟨⟨225,314,68,3384⟩,349597597696,273591980⟩,0,7,1,900773,41⟩
private theorem pass1749_2293 : (Triangular src1749) 2293 2321 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1749_2322 : (Triangular src1749) 2322 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1749 : Cover (Triangular src1749) 2389 2293 [2321,2389] := by
  exact ⟨by decide, by decide, pass1749_2293, by decide, by decide, pass1749_2322, rfl⟩
def src1750 : Request := ⟨⟨⟨275,383,83,3384⟩,635228389376,603020643⟩,1,7,1,900773,41⟩
private theorem pass1750_2293 : (Triangular src1750) 2293 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1750_2329 : (Triangular src1750) 2329 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1750 : Cover (Triangular src1750) 2389 2293 [2328,2389] := by
  exact ⟨by decide, by decide, pass1750_2293, by decide, by decide, pass1750_2329, rfl⟩
def src1751 : Request := ⟨⟨⟨275,383,83,3807⟩,635228389376,603020643⟩,2,7,1,900773,41⟩
private theorem pass1751_2293 : (Triangular src1751) 2293 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1751_2309 : (Triangular src1751) 2309 2369 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1751_2370 : (Triangular src1751) 2370 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1751 : Cover (Triangular src1751) 2389 2293 [2308,2369,2389] := by
  exact ⟨by decide, by decide, pass1751_2293, by decide, by decide, pass1751_2309, by decide, by decide, pass1751_2370, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1699

-- Source: Research6969.PrefixRescueDataHigherHelperCases21
section Z6969Source1700
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases21
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,25⟩
  bank i := ![bank101 4282, bank100 4817, bank100 5419, bank134 6096, bank143 7715, bank193 10983, bank224 22261, bank239 72277, bank307 64247, bank294 475797, bank350 102908] i
  reserve i := ![0, 1, 2, 4, 8, 16, 40, 85, 145, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900773
  seedFloor := 16

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 4282
    · exact rank100 4817
    · exact rank100 5419
    · exact rank134 6096
    · exact rank143 7715
    · exact rank193 10983
    · exact rank224 22261
    · exact rank239 72277
    · exact rank307 64247
    · exact rank294 475797
    · exact rank350 102908
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1727⟩
    · exact ⟨_, cover1728⟩
    · exact ⟨_, cover1729⟩
    · exact ⟨_, cover1730⟩
    · exact ⟨_, cover1731⟩
    · exact ⟨_, cover1732⟩
    · exact ⟨_, cover1733⟩
    · exact ⟨_, cover1734⟩
    · exact ⟨_, cover1735⟩
    · exact ⟨_, cover1736⟩
    · exact ⟨_, cover1737⟩

def price : EarlyPrice := ⟨7, 25, 10, 75/100, 70/100, ![4630610086431, 1144935750581, 21158070202, 5077950936], 1623911835817335⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![10507/191, 78629/123, 960881/246, 1286350/123] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases21
end Z6969Source1700

-- Source: Research6969.PrefixNearSavedHigherHelperCases21
section Z6969Source1701
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases21
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4384,55,639,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases21.plan Lower6960.Prefix6969RescueData.HigherHelperCases21.plan Lower6960.Prefix6969RescueData.HigherHelperCases21.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 7 16 25 900773 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases21.plan, Lower6960.Prefix6969MainCases.HigherHelperCases21.price, Lower6960.Prefix6969MainCases.HigherHelperCases21.valid, Lower6960.Prefix6969MainCases.HigherHelperCases21.priced, Lower6960.Prefix6969MainCases.HigherHelperCases21.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases21.plan, Lower6960.Prefix6969RescueData.HigherHelperCases21.price, Lower6960.Prefix6969RescueData.HigherHelperCases21.sources, Lower6960.Prefix6969RescueData.HigherHelperCases21.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 202825091351954784 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases21
end Z6969Source1701

-- Source: Research6969.PrefixMainDataHigherHelperCases22
section Z6969Source1702
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases22
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 19
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 13, 15, 21, 18, 21, 25, 30, 40, 40, 65, 75, 75] i
  bank i := ![bank3 1490, bank11 1580, bank19 1656, bank24 1838, bank33 1882, bank37 2039, bank45 2316, bank61 2536, bank72 2841, bank65 3612, bank89 4866, bank103 3373, bank123 3616, bank140 3997, bank168 4492, bank122 24063, bank159 6076, bank199 9241, bank172 88577, bank171 201573] i
  head := src1772
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
  historyValues := [![15751, 159363, 728213, 3270395],
    ![12581, 452601/4, 521400, 2496400],
    ![6218, 485413/9, 521400, 2058822],
    ![29433/8, 526299/16, 794566/3, 9140374/9],
    ![65616/25, 558644/25, 203256, 885481],
    ![17323/9, 600253/36, 2702979/16, 10139947/16],
    ![38747/32, 677181/64, 3051094/25, 11517468/25],
    ![96292/121, 784203/121, 3524287/49, 12611528/49],
    ![96292/121, 784203/121, 3524287/49, 12611528/49],
    ![96292/121, 784203/121, 3524287/49, 12611528/49],
    ![66774/121, 2569472/441, 5800455/98, 12611528/49],
    ![66774/121, 2569472/441, 5800455/98, 11377129/49],
    ![66774/121, 627436/121, 2728540/49, 8991184/49],
    ![66774/121, 627436/121, 2728540/49, 8991184/49],
    ![66774/121, 627436/121, 2728540/49, 20178064/121],
    ![41249/100, 627436/121, 2728540/49, 20178064/121],
    ![41249/100, 380639/80, 11432780/243, 120863792/729],
    ![41249/100, 5678170/1323, 21050998/529, 275732958/1849],
    ![1872696/5329, 5678170/1323, 21050998/529, 275732958/1849],
    ![1826342/5329, 5678170/1323, 21050998/529, 275732958/1849]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 7 26 900773 := by
  refine ⟨?_, rank154 4973, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1772⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free11_0
    · exact free19_0
    · exact free24_0
    · exact free33_0
    · exact free37_0
    · exact free45_0
    · exact free61_0
    · exact free72_0
    · exact free65_0
    · exact free89_1
    · exact free103_0
    · exact free123_0
    · exact free140_0
    · exact free168_0
    · exact free122_0
    · exact free159_0
    · exact free199_0
    · exact free172_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [298062459, 296797354, 296738057, 297292253, 297416183, 297094483, 296447619, 107111453, 96432914, 89438481, 88432020, 88287915, 103734583, 103691750, 64285048, 67236324, 94030305, 109182758, 136276803, 231830466], [1200236, 1206708, 1207011, 1204176, 1203542, 1205188, 1208497, 3678292, 4105202, 4443646, 4494399, 4501666, 3797033, 3798841, 6257587, 5974992, 4212094, 3606389, 2851570, 1597584],
  ![123060247962120, 1609360789224, 208647419400, 4296335880], 161926206734173519⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 5678170/1323, 21050998/529, 275732958/1849] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases22
end Z6969Source1702

-- Source: Research6969.PrefixRescueDataHigherHelperCases22
section Z6969Source1703
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases22
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,40⟩
  bank i := ![bank60 4282, bank78 4282, bank101 4817, bank134 6096, bank156 8679, bank218 15636, bank260 50764, bank259 164837, bank320 72277, bank305 1738186, bank294 422931] i
  reserve i := ![0, 1, 3, 6, 13, 32, 110, 145, 190, 245, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900773
  seedFloor := 26

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank60 4282
    · exact rank78 4282
    · exact rank101 4817
    · exact rank134 6096
    · exact rank156 8679
    · exact rank218 15636
    · exact rank260 50764
    · exact rank259 164837
    · exact rank320 72277
    · exact rank305 1738186
    · exact rank294 422931
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1738⟩
    · exact ⟨_, cover1739⟩
    · exact ⟨_, cover1740⟩
    · exact ⟨_, cover1741⟩
    · exact ⟨_, cover1742⟩
    · exact ⟨_, cover1743⟩
    · exact ⟨_, cover1744⟩
    · exact ⟨_, cover1745⟩
    · exact ⟨_, cover1747⟩
    · exact ⟨_, cover1748⟩
    · exact ⟨_, cover1746⟩

def price : EarlyPrice := ⟨7, 40, 10, 70/100, 70/100, ![27066535270804, 4126327785744, 23544431568, 3531675168], 5127675282132990⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![6484/123, 132757/191, 773619/191, 2891080/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases22
end Z6969Source1703

end Merged_Z6969Pack0719

-- merged module Z6969Pack0720
section Merged_Z6969Pack0720

-- Source: Research6969.PrefixNearSavedHigherHelperCases22
section Z6969Source1704
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases22
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4291,52,695,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases22.plan Lower6960.Prefix6969RescueData.HigherHelperCases22.plan Lower6960.Prefix6969RescueData.HigherHelperCases22.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 7 26 40 900773 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases22.plan, Lower6960.Prefix6969MainCases.HigherHelperCases22.price, Lower6960.Prefix6969MainCases.HigherHelperCases22.valid, Lower6960.Prefix6969MainCases.HigherHelperCases22.priced, Lower6960.Prefix6969MainCases.HigherHelperCases22.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases22.plan, Lower6960.Prefix6969RescueData.HigherHelperCases22.price, Lower6960.Prefix6969RescueData.HigherHelperCases22.sources, Lower6960.Prefix6969RescueData.HigherHelperCases22.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 225944364851317453 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases22
end Z6969Source1704

-- Source: Research6969.PrefixMainDataMarkedExitCandidates2
section Z6969Source1705
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.MarkedExitCandidates2
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 11
  reserve i := ![0, 1, 2, 3, 5, 8, 12, 18, 21, 65, 75, 75] i
  bank i := ![bank3 1490, bank11 1580, bank19 1656, bank24 1838, bank37 2039, bank50 2450, bank63 2899, bank89 3732, bank123 3616, bank167 24691, bank215 10166, bank171 201573] i
  head := src1773
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8]
  historyValues := [![15999, 158674, 725391, 3198007],
    ![12581, 433065/4, 521400, 2496400],
    ![6218, 463765/9, 521400, 1840230],
    ![29433/8, 503595/16, 253474, 8169910/9],
    ![17323/9, 573325/36, 2583123/16, 9063355/16],
    ![81680/81, 683200/81, 770665/9, 1500625/4],
    ![81680/81, 683200/81, 770665/9, 8404201/25],
    ![250508/361, 2086760/361, 3067704/49, 1382395/6],
    ![250508/361, 595756/121, 2587036/49, 1148080/7],
    ![55840/147, 595756/121, 2587036/49, 1148080/7],
    ![55840/147, 21400925/5329, 96537819/2500, 25836889/196],
    ![1826342/5329, 21400925/5329, 96537819/2500, 25836889/196]]

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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 7 41 900773 := by
  refine ⟨?_, rank154 4445, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1773⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free11_0
    · exact free19_0
    · exact free24_0
    · exact free37_0
    · exact free50_0
    · exact free63_0
    · exact free89_0
    · exact free123_0
    · exact free167_0
    · exact free215_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [289953773, 288787889, 288382082, 288585773, 288405855, 152048894, 152076826, 152011655, 90143701, 95395549, 139445473, 229863298], [1241718, 1247683, 1249759, 1248717, 1249637, 2532812, 2532348, 2533432, 4408084, 4148984, 2782098, 1613758],
  ![122016035844360, 1611486092192, 206876968200, 4937290960], 159085904816713230⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 21400925/5329, 96537819/2500, 25836889/196] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.MarkedExitCandidates2
end Z6969Source1705

-- Source: Research6969.PrefixRescueDataMarkedExitCandidates2
section Z6969Source1706
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.MarkedExitCandidates2
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,56⟩
  bank i := ![bank59 3384, bank78 3384, bank78 3807, bank100 4282, bank134 5419, bank193 8679, bank225 19788, bank295 50764, bank294 264035, bank335 72277, bank305 1085143] i
  reserve i := ![0, 1, 2, 4, 8, 20, 50, 145, 190, 245, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900773
  seedFloor := 41

theorem sources : plan.Sources 2293 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank59 3384
    · exact rank78 3384
    · exact rank78 3807
    · exact rank100 4282
    · exact rank134 5419
    · exact rank193 8679
    · exact rank225 19788
    · exact rank295 50764
    · exact rank294 264035
    · exact rank335 72277
    · exact rank305 1085143
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1749⟩
    · exact ⟨_, cover1750⟩
    · exact ⟨_, cover1751⟩
    · exact ⟨_, cover1752⟩
    · exact ⟨_, cover1753⟩
    · exact ⟨_, cover1754⟩
    · exact ⟨_, cover1755⟩
    · exact ⟨_, cover1756⟩
    · exact ⟨_, cover1757⟩
    · exact ⟨_, cover1759⟩
    · exact ⟨_, cover1758⟩

def price : EarlyPrice := ⟨7, 56, 10, 65/100, 60/100, ![23656549286914, 2627507649732, 39153514808, 4195032144], 3957381008410032⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![6484/123, 172853/246, 950915/246, 2023756/123] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.MarkedExitCandidates2
end Z6969Source1706

-- Source: Research6969.PrefixNearSavedMarkedExitCandidates2
section Z6969Source1707
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedMarkedExitCandidates2
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4015,52,702,true⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.MarkedExitCandidates2.plan Lower6960.Prefix6969RescueData.MarkedExitCandidates2.plan Lower6960.Prefix6969RescueData.MarkedExitCandidates2.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  exact ⟨by decide, by decide +kernel⟩

def data : NearCase 7 41 56 900773 :=
  ⟨Lower6960.Prefix6969MainCases.MarkedExitCandidates2.plan, Lower6960.Prefix6969MainCases.MarkedExitCandidates2.price, Lower6960.Prefix6969MainCases.MarkedExitCandidates2.valid, Lower6960.Prefix6969MainCases.MarkedExitCandidates2.priced, Lower6960.Prefix6969MainCases.MarkedExitCandidates2.sources,
   Lower6960.Prefix6969RescueData.MarkedExitCandidates2.plan, Lower6960.Prefix6969RescueData.MarkedExitCandidates2.price, Lower6960.Prefix6969RescueData.MarkedExitCandidates2.sources, Lower6960.Prefix6969RescueData.MarkedExitCandidates2.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 197360170479410822 := by
  unfold NearCase.fee
  unfold Exit.extra
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedMarkedExitCandidates2
end Z6969Source1707

-- Source: Research6969.PrefixNearSelect7
section Z6969Source1708
set_option autoImplicit true
namespace Lower6960.Prefix6969Early
set_option maxHeartbeats 8000000

theorem nearChoose7 (j : Fin 56) (ok : UniformAllowed 7 (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧ w≤900773 ∧ ∃ c : NearCase 7 l u w, c.uniform := by
  fin_cases j
  · refine ⟨1, 1, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases17.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases17.fee_exact]; decide +kernel
  · refine ⟨2, 3, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases18.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases18.fee_exact]; decide +kernel
  · refine ⟨2, 3, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases18.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases18.fee_exact]; decide +kernel
  · refine ⟨4, 8, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases19.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases19.fee_exact]; decide +kernel
  · refine ⟨4, 8, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases19.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases19.fee_exact]; decide +kernel
  · refine ⟨4, 8, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases19.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases19.fee_exact]; decide +kernel
  · refine ⟨4, 8, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases19.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases19.fee_exact]; decide +kernel
  · refine ⟨4, 8, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases19.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases19.fee_exact]; decide +kernel
  · refine ⟨9, 15, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases20.fee_exact]; decide +kernel
  · refine ⟨9, 15, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases20.fee_exact]; decide +kernel
  · refine ⟨9, 15, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases20.fee_exact]; decide +kernel
  · refine ⟨9, 15, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases20.fee_exact]; decide +kernel
  · refine ⟨9, 15, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases20.fee_exact]; decide +kernel
  · refine ⟨9, 15, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases20.fee_exact]; decide +kernel
  · refine ⟨9, 15, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases20.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases20.fee_exact]; decide +kernel
  · refine ⟨16, 25, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases21.fee_exact]; decide +kernel
  · refine ⟨16, 25, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases21.fee_exact]; decide +kernel
  · refine ⟨16, 25, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases21.fee_exact]; decide +kernel
  · refine ⟨16, 25, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases21.fee_exact]; decide +kernel
  · refine ⟨16, 25, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases21.fee_exact]; decide +kernel
  · refine ⟨16, 25, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases21.fee_exact]; decide +kernel
  · refine ⟨16, 25, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases21.fee_exact]; decide +kernel
  · refine ⟨16, 25, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases21.fee_exact]; decide +kernel
  · refine ⟨16, 25, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases21.fee_exact]; decide +kernel
  · refine ⟨16, 25, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases21.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases21.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨26, 40, 900773, by decide, by decide, by decide, NearSavedHigherHelperCases22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases22.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel
  · refine ⟨41, 56, 900773, by decide, by decide, by decide, NearSavedMarkedExitCandidates2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedMarkedExitCandidates2.fee_exact]; decide +kernel

end Lower6960.Prefix6969Early
end Z6969Source1708

-- Source: Research6969.PrefixNearRoute
section Z6969Source1709
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Early

open Finset Polynomial
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open Far6969RescueGeometry (Model Family)

theorem choose (a : Fin 6) (j : Fin 56) (ok : UniformAllowed (a.val+2) (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧
        w≤(if a.val=0 then threshold j else (a.val+2)*128682-1) ∧
        ∃ c : NearCase (a.val+2) l u w, c.uniform := by
  fin_cases a
  · exact nearChoose2 j ok
  · exact nearChoose3 j ok
  · exact nearChoose4 j ok
  · exact nearChoose5 j ok
  · exact nearChoose6 j ok
  · exact nearChoose7 j ok

theorem route {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2293≤M.overhead.toNat) (hi : M.overhead.toNat≤2389)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Nonempty (Outcome F Crt) :=
  route_using choose F Crt lo hi noPole residues

end Lower6960.Prefix6969Early
end Z6969Source1709

-- Source: Research6969.OrdSource14
section Z6969Source1710
set_option autoImplicit true
namespace Research6969.OrdSource
set_option maxHeartbeats 0
set_option maxRecDepth 20000
private def src224:PhysicalWindow.Request := ⟨⟨⟨2600,3621,819,45081⟩,546063062138880,4884209183309⟩,195,4,1,514147,161⟩
private theorem ok224_2390:PhysicalWindow.Triangular src224 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover224: PhysicalWindow.Cover (PhysicalWindow.Triangular src224) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok224_2390,rfl⟩
def row224:OrdinaryBounds.Source 2390 2534:=
  ⟨src224,⟨Research6969.PackedRanks.OrdRanks4To5.rank4 45081, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover224⟩⟩
private def src225:PhysicalWindow.Request := ⟨⟨⟨2800,3901,834,40072⟩,653560508579840,6296101689637⟩,195,4,1,514147,161⟩
private theorem ok225_2390:PhysicalWindow.Triangular src225 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover225: PhysicalWindow.Cover (PhysicalWindow.Triangular src225) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok225_2390,rfl⟩
def row225:OrdinaryBounds.Source 2390 2534:=
  ⟨src225,⟨Research6969.PackedRanks.OrdRanks4To5.rank5 40072, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover225⟩⟩
private def src226:PhysicalWindow.Request := ⟨⟨⟨2300,3203,702,45124⟩,369170633195520,2918855628076⟩,195,4,1,514147,257⟩
private theorem ok226_2390:PhysicalWindow.Triangular src226 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover226: PhysicalWindow.Cover (PhysicalWindow.Triangular src226) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok226_2390,rfl⟩
def row226:OrdinaryBounds.Source 2390 2534:=
  ⟨src226,⟨Research6969.PackedRanks.TerminalRanks24To27.rank24 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover226⟩⟩
private def src227:PhysicalWindow.Request := ⟨⟨⟨3000,4178,894,57109⟩,804053213511680,8288484232853⟩,250,4,1,514147,257⟩
private theorem ok227_2390:PhysicalWindow.Triangular src227 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover227: PhysicalWindow.Cover (PhysicalWindow.Triangular src227) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok227_2390,rfl⟩
def row227:OrdinaryBounds.Source 2390 2534:=
  ⟨src227,⟨Research6969.PackedRanks.TerminalRanks72To75.rank75 57109, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover227⟩⟩
private def src228:PhysicalWindow.Request := ⟨⟨⟨2000,2784,610,50419⟩,242679148707840,1666247886835⟩,195,4,1,514147,513⟩
private theorem ok228_2390:PhysicalWindow.Triangular src228 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover228: PhysicalWindow.Cover (PhysicalWindow.Triangular src228) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok228_2390,rfl⟩
def row228:OrdinaryBounds.Source 2390 2534:=
  ⟨src228,⟨Research6969.PackedRanks.TerminalRanks16To19.rank16 50419, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover228⟩⟩
private def src229:PhysicalWindow.Request := ⟨⟨⟨2600,3620,775,63811⟩,523640687820800,4674619806217⟩,250,4,1,514147,513⟩
private theorem ok229_2390:PhysicalWindow.Triangular src229 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover229: PhysicalWindow.Cover (PhysicalWindow.Triangular src229) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok229_2390,rfl⟩
def row229:OrdinaryBounds.Source 2390 2534:=
  ⟨src229,⟨Research6969.PackedRanks.TerminalRanks36To39.rank38 63811, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover229⟩⟩
private def src230:PhysicalWindow.Request := ⟨⟨⟨1450,2018,432,49853⟩,90926432911360,452250342305⟩,150,4,1,514147,1025⟩
private theorem ok230_2390:PhysicalWindow.Triangular src230 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover230: PhysicalWindow.Cover (PhysicalWindow.Triangular src230) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok230_2390,rfl⟩
def row230:OrdinaryBounds.Source 2390 2534:=
  ⟨src230,⟨Research6969.PackedRanks.TerminalRanks4To7.rank5 49853, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover230⟩⟩
private def src231:PhysicalWindow.Request := ⟨⟨⟨3000,4175,894,113694⟩,804053213511680,8269353083383⟩,325,4,1,514147,1025⟩
private theorem ok231_2390:PhysicalWindow.Triangular src231 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover231: PhysicalWindow.Cover (PhysicalWindow.Triangular src231) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok231_2390,rfl⟩
def row231:OrdinaryBounds.Source 2390 2534:=
  ⟨src231,⟨Research6969.PackedRanks.TerminalRanks72To75.rank74 113694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover231⟩⟩
private def src232:PhysicalWindow.Request := ⟨⟨⟨2800,3896,854,112233⟩,665461916958720,6387110095257⟩,325,4,1,514147,2049⟩
private theorem ok232_2390:PhysicalWindow.Triangular src232 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover232: PhysicalWindow.Cover (PhysicalWindow.Triangular src232) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok232_2390,rfl⟩
def row232:OrdinaryBounds.Source 2390 2534:=
  ⟨src232,⟨Research6969.PackedRanks.TerminalRanks56To59.rank57 112233, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover232⟩⟩
private def src233:PhysicalWindow.Request := ⟨⟨⟨1000,1391,305,54645⟩,30406634373120,104212783664⟩,115,4,1,514147,4097⟩
private theorem ok233_2390:PhysicalWindow.Triangular src233 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover233: PhysicalWindow.Cover (PhysicalWindow.Triangular src233) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok233_2390,rfl⟩
def row233:OrdinaryBounds.Source 2390 2534:=
  ⟨src233,⟨Research6969.PackedRanks.TerminalRanks0To3.rank2 54645, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover233⟩⟩
private def src234:PhysicalWindow.Request := ⟨⟨⟨2000,2782,610,175105⟩,242679148707840,1662397981334⟩,250,4,1,514147,8193⟩
private theorem ok234_2390:PhysicalWindow.Triangular src234 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover234: PhysicalWindow.Cover (PhysicalWindow.Triangular src234) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok234_2390,rfl⟩
def row234:OrdinaryBounds.Source 2390 2534:=
  ⟨src234,⟨Research6969.PackedRanks.TerminalRanks12To15.rank15 175105, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover234⟩⟩
private def src235:PhysicalWindow.Request := ⟨⟨⟨1200,1669,378,121332⟩,53798525730816,221264762670⟩,150,4,1,514147,16385⟩
private theorem ok235_2390:PhysicalWindow.Triangular src235 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover235: PhysicalWindow.Cover (PhysicalWindow.Triangular src235) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok235_2390,rfl⟩
def row235:OrdinaryBounds.Source 2390 2534:=
  ⟨src235,⟨Research6969.PackedRanks.OrdRanks0To3.rank1 121332, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover235⟩⟩
private def src236:PhysicalWindow.Request := ⟨⟨⟨1200,1669,366,119707⟩,52501327642624,215795999824⟩,150,4,1,514147,32769⟩
private theorem ok236_2390:PhysicalWindow.Triangular src236 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover236: PhysicalWindow.Cover (PhysicalWindow.Triangular src236) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok236_2390,rfl⟩
def row236:OrdinaryBounds.Source 2390 2534:=
  ⟨src236,⟨Research6969.PackedRanks.TerminalRanks0To3.rank3 119707, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover236⟩⟩
private def src237:PhysicalWindow.Request := ⟨⟨⟨2300,3208,702,64247⟩,369170633195520,2933547980091⟩,45,5,1,642684,1⟩
private theorem ok237_2390:PhysicalWindow.Triangular src237 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover237: PhysicalWindow.Cover (PhysicalWindow.Triangular src237) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok237_2390,rfl⟩
def row237:OrdinaryBounds.Source 2390 2534:=
  ⟨src237,⟨Research6969.PackedRanks.TerminalRanks32To35.rank33 64247, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover237⟩⟩
private def src238:PhysicalWindow.Request := ⟨⟨⟨2800,3905,854,81311⟩,665461916958720,6434729640882⟩,63,5,1,642684,3⟩
private theorem ok238_2390:PhysicalWindow.Triangular src238 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover238: PhysicalWindow.Cover (PhysicalWindow.Triangular src238) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok238_2390,rfl⟩
def row238:OrdinaryBounds.Source 2390 2534:=
  ⟨src238,⟨Research6969.PackedRanks.TerminalRanks64To67.rank66 81311, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover238⟩⟩
private def src239:PhysicalWindow.Request := ⟨⟨⟨2300,3208,702,57109⟩,369170633195520,2933547980091⟩,45,5,1,642684,6⟩
private theorem ok239_2390:PhysicalWindow.Triangular src239 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover239: PhysicalWindow.Cover (PhysicalWindow.Triangular src239) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok239_2390,rfl⟩
def row239:OrdinaryBounds.Source 2390 2534:=
  ⟨src239,⟨Research6969.PackedRanks.TerminalRanks32To35.rank33 57109, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover239⟩⟩
end Research6969.OrdSource
end Z6969Source1710

-- Source: Research6969.OrdSource15
section Z6969Source1711
set_option autoImplicit true
namespace Research6969.OrdSource
set_option maxHeartbeats 0
set_option maxRecDepth 20000
private def src240:PhysicalWindow.Request := ⟨⟨⟨2600,3626,793,72277⟩,532875289296896,4784491173220⟩,63,5,1,642684,10⟩
private theorem ok240_2390:PhysicalWindow.Triangular src240 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover240: PhysicalWindow.Cover (PhysicalWindow.Triangular src240) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok240_2390,rfl⟩
def row240:OrdinaryBounds.Source 2390 2534:=
  ⟨src240,⟨Research6969.PackedRanks.TerminalRanks48To51.rank48 72277, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover240⟩⟩
private def src241:PhysicalWindow.Request := ⟨⟨⟨2800,3905,854,57109⟩,665461916958720,6434729640882⟩,63,5,1,642684,15⟩
private theorem ok241_2390:PhysicalWindow.Triangular src241 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover241: PhysicalWindow.Cover (PhysicalWindow.Triangular src241) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok241_2390,rfl⟩
def row241:OrdinaryBounds.Source 2390 2534:=
  ⟨src241,⟨Research6969.PackedRanks.TerminalRanks64To67.rank66 57109, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover241⟩⟩
private def src242:PhysicalWindow.Request := ⟨⟨⟨2800,3905,854,45124⟩,665461916958720,6434729640882⟩,63,5,1,642684,21⟩
private theorem ok242_2390:PhysicalWindow.Triangular src242 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover242: PhysicalWindow.Cover (PhysicalWindow.Triangular src242) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok242_2390,rfl⟩
def row242:OrdinaryBounds.Source 2390 2534:=
  ⟨src242,⟨Research6969.PackedRanks.TerminalRanks64To67.rank66 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover242⟩⟩
private def src243:PhysicalWindow.Request := ⟨⟨⟨2600,3626,819,35655⟩,546063062138880,4905972788959⟩,63,5,1,642684,27⟩
private theorem ok243_2390:PhysicalWindow.Triangular src243 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover243: PhysicalWindow.Cover (PhysicalWindow.Triangular src243) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok243_2390,rfl⟩
def row243:OrdinaryBounds.Source 2390 2534:=
  ⟨src243,⟨Research6969.TransitionBanks.rank265 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover243⟩⟩
private def src244:PhysicalWindow.Request := ⟨⟨⟨2800,3905,882,35655⟩,681932636815360,6598128215989⟩,85,5,1,642684,36⟩
private theorem ok244_2390:PhysicalWindow.Triangular src244 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover244: PhysicalWindow.Cover (PhysicalWindow.Triangular src244) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok244_2390,rfl⟩
def row244:OrdinaryBounds.Source 2390 2534:=
  ⟨src244,⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover244⟩⟩
private def src245:PhysicalWindow.Request := ⟨⟨⟨2300,3207,724,28173⟩,377903408742400,3001726552718⟩,85,5,1,642684,48⟩
private theorem ok245_2390:PhysicalWindow.Triangular src245 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover245: PhysicalWindow.Cover (PhysicalWindow.Triangular src245) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok245_2390,rfl⟩
def row245:OrdinaryBounds.Source 2390 2534:=
  ⟨src245,⟨Research6969.PackedRanks.TerminalRanks32To35.rank32 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover245⟩⟩
private def src246:PhysicalWindow.Request := ⟨⟨⟨2600,3624,819,28173⟩,546063062138880,4897259437389⟩,115,5,1,642684,65⟩
private theorem ok246_2390:PhysicalWindow.Triangular src246 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover246: PhysicalWindow.Cover (PhysicalWindow.Triangular src246) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok246_2390,rfl⟩
def row246:OrdinaryBounds.Source 2390 2534:=
  ⟨src246,⟨Research6969.PackedRanks.TerminalRanks44To47.rank44 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover246⟩⟩
private def src247:PhysicalWindow.Request := ⟨⟨⟨2600,3623,793,35655⟩,532875289296896,4771760428124⟩,150,5,1,642684,97⟩
private theorem ok247_2390:PhysicalWindow.Triangular src247 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover247: PhysicalWindow.Cover (PhysicalWindow.Triangular src247) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok247_2390,rfl⟩
def row247:OrdinaryBounds.Source 2390 2534:=
  ⟨src247,⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover247⟩⟩
private def src248:PhysicalWindow.Request := ⟨⟨⟨2800,3901,834,40072⟩,653560508579840,6296101689637⟩,195,5,1,642684,161⟩
private theorem ok248_2390:PhysicalWindow.Triangular src248 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover248: PhysicalWindow.Cover (PhysicalWindow.Triangular src248) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok248_2390,rfl⟩
def row248:OrdinaryBounds.Source 2390 2534:=
  ⟨src248,⟨Research6969.PackedRanks.OrdRanks4To5.rank5 40072, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover248⟩⟩
private def src249:PhysicalWindow.Request := ⟨⟨⟨3000,4178,894,57109⟩,804053213511680,8288484232853⟩,250,5,1,642684,257⟩
private theorem ok249_2390:PhysicalWindow.Triangular src249 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover249: PhysicalWindow.Cover (PhysicalWindow.Triangular src249) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok249_2390,rfl⟩
def row249:OrdinaryBounds.Source 2390 2534:=
  ⟨src249,⟨Research6969.PackedRanks.TerminalRanks72To75.rank75 57109, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover249⟩⟩
private def src250:PhysicalWindow.Request := ⟨⟨⟨2000,2784,610,50419⟩,242679148707840,1666247886835⟩,195,5,1,642684,513⟩
private theorem ok250_2390:PhysicalWindow.Triangular src250 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover250: PhysicalWindow.Cover (PhysicalWindow.Triangular src250) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok250_2390,rfl⟩
def row250:OrdinaryBounds.Source 2390 2534:=
  ⟨src250,⟨Research6969.PackedRanks.TerminalRanks16To19.rank16 50419, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover250⟩⟩
private def src251:PhysicalWindow.Request := ⟨⟨⟨2600,3620,775,63811⟩,523640687820800,4674619806217⟩,250,5,1,642684,513⟩
private theorem ok251_2390:PhysicalWindow.Triangular src251 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover251: PhysicalWindow.Cover (PhysicalWindow.Triangular src251) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok251_2390,rfl⟩
def row251:OrdinaryBounds.Source 2390 2534:=
  ⟨src251,⟨Research6969.PackedRanks.TerminalRanks36To39.rank38 63811, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover251⟩⟩
private def src252:PhysicalWindow.Request := ⟨⟨⟨3000,4175,894,113694⟩,804053213511680,8269353083383⟩,325,5,1,642684,1025⟩
private theorem ok252_2390:PhysicalWindow.Triangular src252 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover252: PhysicalWindow.Cover (PhysicalWindow.Triangular src252) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok252_2390,rfl⟩
def row252:OrdinaryBounds.Source 2390 2534:=
  ⟨src252,⟨Research6969.PackedRanks.TerminalRanks72To75.rank74 113694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover252⟩⟩
private def src253:PhysicalWindow.Request := ⟨⟨⟨2800,3896,812,157727⟩,640331821875200,6140432144913⟩,325,5,1,642684,4097⟩
private theorem ok253_2390:PhysicalWindow.Triangular src253 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover253: PhysicalWindow.Cover (PhysicalWindow.Triangular src253) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok253_2390,rfl⟩
def row253:OrdinaryBounds.Source 2390 2534:=
  ⟨src253,⟨Research6969.PackedRanks.TerminalRanks56To59.rank56 157727, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover253⟩⟩
private def src254:PhysicalWindow.Request := ⟨⟨⟨2000,2782,610,175105⟩,242679148707840,1662397981334⟩,250,5,1,642684,8193⟩
private theorem ok254_2390:PhysicalWindow.Triangular src254 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover254: PhysicalWindow.Cover (PhysicalWindow.Triangular src254) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok254_2390,rfl⟩
def row254:OrdinaryBounds.Source 2390 2534:=
  ⟨src254,⟨Research6969.PackedRanks.TerminalRanks12To15.rank15 175105, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover254⟩⟩
private def src255:PhysicalWindow.Request := ⟨⟨⟨2000,2782,596,194349⟩,238428431581184,1632591172707⟩,250,5,1,642684,16385⟩
private theorem ok255_2390:PhysicalWindow.Triangular src255 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover255: PhysicalWindow.Cover (PhysicalWindow.Triangular src255) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok255_2390,rfl⟩
def row255:OrdinaryBounds.Source 2390 2534:=
  ⟨src255,⟨Research6969.PackedRanks.TerminalRanks12To15.rank14 194349, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover255⟩⟩
end Research6969.OrdSource
end Z6969Source1711

-- Source: Research6969.OrdSource16
section Z6969Source1712
set_option autoImplicit true
namespace Research6969.OrdSource
set_option maxHeartbeats 0
set_option maxRecDepth 20000
private def src256:PhysicalWindow.Request := ⟨⟨⟨1200,1669,366,119707⟩,52501327642624,215795999824⟩,150,5,1,642684,32769⟩
private theorem ok256_2390:PhysicalWindow.Triangular src256 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover256: PhysicalWindow.Cover (PhysicalWindow.Triangular src256) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok256_2390,rfl⟩
def row256:OrdinaryBounds.Source 2390 2534:=
  ⟨src256,⟨Research6969.PackedRanks.TerminalRanks0To3.rank3 119707, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover256⟩⟩
private def src257:PhysicalWindow.Request := ⟨⟨⟨2800,3905,854,72277⟩,665461916958720,6434729640882⟩,85,6,1,771221,1⟩
private theorem ok257_2390:PhysicalWindow.Triangular src257 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover257: PhysicalWindow.Cover (PhysicalWindow.Triangular src257) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok257_2390,rfl⟩
def row257:OrdinaryBounds.Source 2390 2534:=
  ⟨src257,⟨Research6969.PackedRanks.TerminalRanks64To67.rank66 72277, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover257⟩⟩
private def src258:PhysicalWindow.Request := ⟨⟨⟨2300,3207,724,50764⟩,377903408742400,3001726552718⟩,63,6,1,771221,3⟩
private theorem ok258_2390:PhysicalWindow.Triangular src258 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover258: PhysicalWindow.Cover (PhysicalWindow.Triangular src258) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok258_2390,rfl⟩
def row258:OrdinaryBounds.Source 2390 2534:=
  ⟨src258,⟨Research6969.PackedRanks.TerminalRanks32To35.rank32 50764, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover258⟩⟩
private def src259:PhysicalWindow.Request := ⟨⟨⟨2800,3905,882,64247⟩,681932636815360,6598128215989⟩,85,6,1,771221,6⟩
private theorem ok259_2390:PhysicalWindow.Triangular src259 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover259: PhysicalWindow.Cover (PhysicalWindow.Triangular src259) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok259_2390,rfl⟩
def row259:OrdinaryBounds.Source 2390 2534:=
  ⟨src259,⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 64247, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover259⟩⟩
private def src260:PhysicalWindow.Request := ⟨⟨⟨2300,3207,702,45124⟩,369170633195520,2930605494152⟩,63,6,1,771221,10⟩
private theorem ok260_2390:PhysicalWindow.Triangular src260 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover260: PhysicalWindow.Cover (PhysicalWindow.Triangular src260) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok260_2390,rfl⟩
def row260:OrdinaryBounds.Source 2390 2534:=
  ⟨src260,⟨Research6969.PackedRanks.TerminalRanks28To31.rank31 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover260⟩⟩
private def src261:PhysicalWindow.Request := ⟨⟨⟨2300,3207,702,40111⟩,369170633195520,2930605494152⟩,63,6,1,771221,15⟩
private theorem ok261_2390:PhysicalWindow.Triangular src261 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover261: PhysicalWindow.Cover (PhysicalWindow.Triangular src261) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok261_2390,rfl⟩
def row261:OrdinaryBounds.Source 2390 2534:=
  ⟨src261,⟨Research6969.PackedRanks.TerminalRanks28To31.rank31 40111, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover261⟩⟩
private def src262:PhysicalWindow.Request := ⟨⟨⟨2800,3905,882,45124⟩,681932636815360,6598128215989⟩,85,6,1,771221,21⟩
private theorem ok262_2390:PhysicalWindow.Triangular src262 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover262: PhysicalWindow.Cover (PhysicalWindow.Triangular src262) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok262_2390,rfl⟩
def row262:OrdinaryBounds.Source 2390 2534:=
  ⟨src262,⟨Research6969.PackedRanks.TerminalRanks64To67.rank67 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover262⟩⟩
private def src263:PhysicalWindow.Request := ⟨⟨⟨2600,3625,819,40111⟩,546063062138880,4901614794409⟩,85,6,1,771221,27⟩
private theorem ok263_2390:PhysicalWindow.Triangular src263 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover263: PhysicalWindow.Cover (PhysicalWindow.Triangular src263) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok263_2390,rfl⟩
def row263:OrdinaryBounds.Source 2390 2534:=
  ⟨src263,⟨Research6969.TransitionBanks.rank263 40111, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover263⟩⟩
private def src264:PhysicalWindow.Request := ⟨⟨⟨2300,3207,702,35655⟩,369170633195520,2930605494152⟩,85,6,1,771221,36⟩
private theorem ok264_2390:PhysicalWindow.Triangular src264 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover264: PhysicalWindow.Cover (PhysicalWindow.Triangular src264) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok264_2390,rfl⟩
def row264:OrdinaryBounds.Source 2390 2534:=
  ⟨src264,⟨Research6969.PackedRanks.TerminalRanks28To31.rank31 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover264⟩⟩
private def src265:PhysicalWindow.Request := ⟨⟨⟨2800,3903,882,35655⟩,681932636815360,6587245977411⟩,115,6,1,771221,48⟩
private theorem ok265_2390:PhysicalWindow.Triangular src265 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover265: PhysicalWindow.Cover (PhysicalWindow.Triangular src265) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok265_2390,rfl⟩
def row265:OrdinaryBounds.Source 2390 2534:=
  ⟨src265,⟨Research6969.PackedRanks.TerminalRanks64To67.rank65 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover265⟩⟩
private def src266:PhysicalWindow.Request := ⟨⟨⟨2300,3206,724,31694⟩,377903408742400,2998712046218⟩,115,6,1,771221,65⟩
private theorem ok266_2390:PhysicalWindow.Triangular src266 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover266: PhysicalWindow.Cover (PhysicalWindow.Triangular src266) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok266_2390,rfl⟩
def row266:OrdinaryBounds.Source 2390 2534:=
  ⟨src266,⟨Research6969.PackedRanks.TerminalRanks28To31.rank29 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover266⟩⟩
private def src267:PhysicalWindow.Request := ⟨⟨⟨2600,3623,793,31694⟩,532875289296896,4771760428124⟩,150,6,1,771221,97⟩
private theorem ok267_2390:PhysicalWindow.Triangular src267 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover267: PhysicalWindow.Cover (PhysicalWindow.Triangular src267) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok267_2390,rfl⟩
def row267:OrdinaryBounds.Source 2390 2534:=
  ⟨src267,⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover267⟩⟩
private def src268:PhysicalWindow.Request := ⟨⟨⟨2600,3621,793,45081⟩,532875289296896,4763286079225⟩,195,6,1,771221,161⟩
private theorem ok268_2390:PhysicalWindow.Triangular src268 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover268: PhysicalWindow.Cover (PhysicalWindow.Triangular src268) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok268_2390,rfl⟩
def row268:OrdinaryBounds.Source 2390 2534:=
  ⟨src268,⟨Research6969.PackedRanks.OrdRanks0To3.rank3 45081, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover268⟩⟩
private def src269:PhysicalWindow.Request := ⟨⟨⟨3000,4178,894,57109⟩,804053213511680,8288484232853⟩,250,6,1,771221,257⟩
private theorem ok269_2390:PhysicalWindow.Triangular src269 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover269: PhysicalWindow.Cover (PhysicalWindow.Triangular src269) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok269_2390,rfl⟩
def row269:OrdinaryBounds.Source 2390 2534:=
  ⟨src269,⟨Research6969.PackedRanks.TerminalRanks72To75.rank75 57109, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover269⟩⟩
private def src270:PhysicalWindow.Request := ⟨⟨⟨2600,3620,775,63811⟩,523640687820800,4674619806217⟩,250,6,1,771221,513⟩
private theorem ok270_2390:PhysicalWindow.Triangular src270 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover270: PhysicalWindow.Cover (PhysicalWindow.Triangular src270) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok270_2390,rfl⟩
def row270:OrdinaryBounds.Source 2390 2534:=
  ⟨src270,⟨Research6969.PackedRanks.TerminalRanks36To39.rank38 63811, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover270⟩⟩
private def src271:PhysicalWindow.Request := ⟨⟨⟨3000,4175,894,113694⟩,804053213511680,8269353083383⟩,325,6,1,771221,1025⟩
private theorem ok271_2390:PhysicalWindow.Triangular src271 2390 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover271: PhysicalWindow.Cover (PhysicalWindow.Triangular src271) 2534 2390 [2534] :=
  ⟨by decide,by decide,ok271_2390,rfl⟩
def row271:OrdinaryBounds.Source 2390 2534:=
  ⟨src271,⟨Research6969.PackedRanks.TerminalRanks72To75.rank74 113694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover271⟩⟩
end Research6969.OrdSource
end Z6969Source1712

-- Source: Research6969.OrdChecks013
section Z6969Source1713
set_option autoImplicit true
namespace Research6969.OrdReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell715:OrdinaryCell.Row 2390 2534:=⟨22,22,9,2,27,some 35,257073,[OrdSource.row153],.marked⟩
theorem checked715:cell715.check OrdinaryBooks.middle 342:=by decide +kernel
def cell716:OrdinaryCell.Row 2390 2534:=⟨22,22,9,2,21,some 26,257073,[],.surface⟩
theorem checked716:cell716.check OrdinaryBooks.middle 342:=by decide +kernel
def cell717:OrdinaryCell.Row 2390 2534:=⟨22,22,9,2,15,some 20,257073,[],.surface⟩
theorem checked717:cell717.check OrdinaryBooks.middle 342:=by decide +kernel
def cell718:OrdinaryCell.Row 2390 2534:=⟨22,22,9,2,10,some 14,257073,[],.surface⟩
theorem checked718:cell718.check OrdinaryBooks.middle 342:=by decide +kernel
def cell719:OrdinaryCell.Row 2390 2534:=⟨22,22,9,2,6,some 9,257073,[],.surface⟩
theorem checked719:cell719.check OrdinaryBooks.middle 342:=by decide +kernel
def cell720:OrdinaryCell.Row 2390 2534:=⟨22,22,9,2,3,some 5,257073,[],.surface⟩
theorem checked720:cell720.check OrdinaryBooks.middle 342:=by decide +kernel
def cell721:OrdinaryCell.Row 2390 2534:=⟨22,22,9,2,1,some 2,257073,[],.surface⟩
theorem checked721:cell721.check OrdinaryBooks.middle 342:=by decide +kernel
def cell722:OrdinaryCell.Row 2390 2534:=⟨22,22,9,2,0,some 0,257073,[],.ambient⟩
theorem checked722:cell722.check OrdinaryBooks.middle 342:=by decide +kernel
def cell723:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,32769,none,385610,[OrdSource.row211],.excluded⟩
theorem checked723:cell723.check OrdinaryBooks.middle 342:=by decide +kernel
def cell724:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,16385,some 32768,385610,[OrdSource.row210],.excluded⟩
theorem checked724:cell724.check OrdinaryBooks.middle 342:=by decide +kernel
def cell725:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,8193,some 16384,385610,[OrdSource.row209],.excluded⟩
theorem checked725:cell725.check OrdinaryBooks.middle 342:=by decide +kernel
def cell726:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,4097,some 8192,385610,[OrdSource.row208],.marked⟩
theorem checked726:cell726.check OrdinaryBooks.middle 342:=by decide +kernel
def cell727:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,2049,some 4096,385610,[OrdSource.row207],.marked⟩
theorem checked727:cell727.check OrdinaryBooks.middle 342:=by decide +kernel
def cell728:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,1025,some 2048,385610,[OrdSource.row205,OrdSource.row206],.marked⟩
theorem checked728:cell728.check OrdinaryBooks.middle 342:=by decide +kernel
def cell729:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,513,some 1024,385610,[OrdSource.row204],.marked⟩
theorem checked729:cell729.check OrdinaryBooks.middle 342:=by decide +kernel
def cell730:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,257,some 512,385610,[OrdSource.row203],.marked⟩
theorem checked730:cell730.check OrdinaryBooks.middle 342:=by decide +kernel
def cell731:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,161,some 256,385610,[OrdSource.row201],.marked⟩
theorem checked731:cell731.check OrdinaryBooks.middle 342:=by decide +kernel
def cell732:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,97,some 160,385610,[OrdSource.row200],.marked⟩
theorem checked732:cell732.check OrdinaryBooks.middle 342:=by decide +kernel
def cell733:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,65,some 96,385610,[OrdSource.row198],.marked⟩
theorem checked733:cell733.check OrdinaryBooks.middle 342:=by decide +kernel
def cell734:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,48,some 64,385610,[OrdSource.row196],.marked⟩
theorem checked734:cell734.check OrdinaryBooks.middle 342:=by decide +kernel
def cell735:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,36,some 47,385610,[OrdSource.row194],.marked⟩
theorem checked735:cell735.check OrdinaryBooks.middle 342:=by decide +kernel
def cell736:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,27,some 35,385610,[OrdSource.row192],.marked⟩
theorem checked736:cell736.check OrdinaryBooks.middle 342:=by decide +kernel
def cell737:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,21,some 26,385610,[OrdSource.row190],.marked⟩
theorem checked737:cell737.check OrdinaryBooks.middle 342:=by decide +kernel
def cell738:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,15,some 20,385610,[OrdSource.row187],.marked⟩
theorem checked738:cell738.check OrdinaryBooks.middle 342:=by decide +kernel
def cell739:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,13,some 14,385610,[OrdSource.row186],.surface⟩
theorem checked739:cell739.check OrdinaryBooks.middle 342:=by decide +kernel
def cell740:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,10,some 12,385610,[],.surface⟩
theorem checked740:cell740.check OrdinaryBooks.middle 342:=by decide +kernel
def cell741:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,6,some 9,385610,[],.surface⟩
theorem checked741:cell741.check OrdinaryBooks.middle 342:=by decide +kernel
def cell742:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,3,some 5,385610,[],.surface⟩
theorem checked742:cell742.check OrdinaryBooks.middle 342:=by decide +kernel
def cell743:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,1,some 2,385610,[],.surface⟩
theorem checked743:cell743.check OrdinaryBooks.middle 342:=by decide +kernel
def cell744:OrdinaryCell.Row 2390 2534:=⟨22,22,9,3,0,some 0,385610,[],.ambient⟩
theorem checked744:cell744.check OrdinaryBooks.middle 342:=by decide +kernel
def cell745:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,32769,none,514147,[OrdSource.row236],.marked⟩
theorem checked745:cell745.check OrdinaryBooks.middle 342:=by decide +kernel
def cell746:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,16385,some 32768,514147,[OrdSource.row235],.marked⟩
theorem checked746:cell746.check OrdinaryBooks.middle 342:=by decide +kernel
def cell747:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,8193,some 16384,514147,[OrdSource.row234],.marked⟩
theorem checked747:cell747.check OrdinaryBooks.middle 342:=by decide +kernel
def cell748:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,4097,some 8192,514147,[OrdSource.row233],.marked⟩
theorem checked748:cell748.check OrdinaryBooks.middle 342:=by decide +kernel
def cell749:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,2049,some 4096,514147,[OrdSource.row232],.marked⟩
theorem checked749:cell749.check OrdinaryBooks.middle 342:=by decide +kernel
def cell750:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,1025,some 2048,514147,[OrdSource.row230,OrdSource.row231],.marked⟩
theorem checked750:cell750.check OrdinaryBooks.middle 342:=by decide +kernel
def cell751:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,513,some 1024,514147,[OrdSource.row229],.marked⟩
theorem checked751:cell751.check OrdinaryBooks.middle 342:=by decide +kernel
def cell752:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,257,some 512,514147,[OrdSource.row227],.marked⟩
theorem checked752:cell752.check OrdinaryBooks.middle 342:=by decide +kernel
def cell753:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,161,some 256,514147,[OrdSource.row225],.marked⟩
theorem checked753:cell753.check OrdinaryBooks.middle 342:=by decide +kernel
def cell754:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,97,some 160,514147,[OrdSource.row223],.marked⟩
theorem checked754:cell754.check OrdinaryBooks.middle 342:=by decide +kernel
def cell755:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,65,some 96,514147,[OrdSource.row221],.marked⟩
theorem checked755:cell755.check OrdinaryBooks.middle 342:=by decide +kernel
def cell756:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,48,some 64,514147,[OrdSource.row220],.marked⟩
theorem checked756:cell756.check OrdinaryBooks.middle 342:=by decide +kernel
def cell757:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,36,some 47,514147,[OrdSource.row219],.marked⟩
theorem checked757:cell757.check OrdinaryBooks.middle 342:=by decide +kernel
def cell758:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,27,some 35,514147,[OrdSource.row218],.marked⟩
theorem checked758:cell758.check OrdinaryBooks.middle 342:=by decide +kernel
def cell759:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,21,some 26,514147,[OrdSource.row217],.marked⟩
theorem checked759:cell759.check OrdinaryBooks.middle 342:=by decide +kernel
def cell760:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,15,some 20,514147,[OrdSource.row216],.marked⟩
theorem checked760:cell760.check OrdinaryBooks.middle 342:=by decide +kernel
def cell761:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,10,some 14,514147,[OrdSource.row215],.marked⟩
theorem checked761:cell761.check OrdinaryBooks.middle 342:=by decide +kernel
def cell762:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,6,some 9,514147,[OrdSource.row214],.surface⟩
theorem checked762:cell762.check OrdinaryBooks.middle 342:=by decide +kernel
def cell763:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,3,some 5,514147,[OrdSource.row213],.surface⟩
theorem checked763:cell763.check OrdinaryBooks.middle 342:=by decide +kernel
def cell764:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,1,some 2,514147,[OrdSource.row212],.surface⟩
theorem checked764:cell764.check OrdinaryBooks.middle 342:=by decide +kernel
def cell765:OrdinaryCell.Row 2390 2534:=⟨22,22,9,4,0,some 0,514147,[],.ambient⟩
theorem checked765:cell765.check OrdinaryBooks.middle 342:=by decide +kernel
def cell766:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,32769,none,642684,[OrdSource.row256],.marked⟩
theorem checked766:cell766.check OrdinaryBooks.middle 342:=by decide +kernel
def cell767:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,16385,some 32768,642684,[OrdSource.row255],.marked⟩
theorem checked767:cell767.check OrdinaryBooks.middle 342:=by decide +kernel
def cell768:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,8193,some 16384,642684,[OrdSource.row254],.marked⟩
theorem checked768:cell768.check OrdinaryBooks.middle 342:=by decide +kernel
def cell769:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,4097,some 8192,642684,[OrdSource.row253],.marked⟩
theorem checked769:cell769.check OrdinaryBooks.middle 342:=by decide +kernel
end Research6969.OrdReceipts
end Z6969Source1713

-- Source: Research6969.OrdChecks014
section Z6969Source1714
set_option autoImplicit true
namespace Research6969.OrdReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell770:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,2049,some 4096,642684,[],.marked⟩
theorem checked770:cell770.check OrdinaryBooks.middle 342:=by decide +kernel
def cell771:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,1537,some 2048,642684,[],.marked⟩
theorem checked771:cell771.check OrdinaryBooks.middle 342:=by decide +kernel
def cell772:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,1025,some 1536,642684,[OrdSource.row252],.marked⟩
theorem checked772:cell772.check OrdinaryBooks.middle 342:=by decide +kernel
def cell773:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,513,some 1024,642684,[OrdSource.row251],.marked⟩
theorem checked773:cell773.check OrdinaryBooks.middle 342:=by decide +kernel
def cell774:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,257,some 512,642684,[OrdSource.row249],.marked⟩
theorem checked774:cell774.check OrdinaryBooks.middle 342:=by decide +kernel
def cell775:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,161,some 256,642684,[OrdSource.row248],.marked⟩
theorem checked775:cell775.check OrdinaryBooks.middle 342:=by decide +kernel
def cell776:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,97,some 160,642684,[OrdSource.row247],.marked⟩
theorem checked776:cell776.check OrdinaryBooks.middle 342:=by decide +kernel
def cell777:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,65,some 96,642684,[OrdSource.row246],.marked⟩
theorem checked777:cell777.check OrdinaryBooks.middle 342:=by decide +kernel
def cell778:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,48,some 64,642684,[OrdSource.row245],.marked⟩
theorem checked778:cell778.check OrdinaryBooks.middle 342:=by decide +kernel
def cell779:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,36,some 47,642684,[OrdSource.row244],.marked⟩
theorem checked779:cell779.check OrdinaryBooks.middle 342:=by decide +kernel
def cell780:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,27,some 35,642684,[OrdSource.row243],.marked⟩
theorem checked780:cell780.check OrdinaryBooks.middle 342:=by decide +kernel
def cell781:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,21,some 26,642684,[OrdSource.row242],.marked⟩
theorem checked781:cell781.check OrdinaryBooks.middle 342:=by decide +kernel
def cell782:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,15,some 20,642684,[OrdSource.row241],.marked⟩
theorem checked782:cell782.check OrdinaryBooks.middle 342:=by decide +kernel
def cell783:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,10,some 14,642684,[OrdSource.row240],.marked⟩
theorem checked783:cell783.check OrdinaryBooks.middle 342:=by decide +kernel
def cell784:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,6,some 9,642684,[OrdSource.row239],.marked⟩
theorem checked784:cell784.check OrdinaryBooks.middle 342:=by decide +kernel
def cell785:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,3,some 5,642684,[OrdSource.row238],.surface⟩
theorem checked785:cell785.check OrdinaryBooks.middle 342:=by decide +kernel
def cell786:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,1,some 2,642684,[OrdSource.row237],.surface⟩
theorem checked786:cell786.check OrdinaryBooks.middle 342:=by decide +kernel
def cell787:OrdinaryCell.Row 2390 2534:=⟨22,22,9,5,0,some 0,642684,[],.ambient⟩
theorem checked787:cell787.check OrdinaryBooks.middle 342:=by decide +kernel
def cell788:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,32769,none,771221,[],.marked⟩
theorem checked788:cell788.check OrdinaryBooks.middle 342:=by decide +kernel
def cell789:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,16385,some 32768,771221,[],.marked⟩
theorem checked789:cell789.check OrdinaryBooks.middle 342:=by decide +kernel
def cell790:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,8193,some 16384,771221,[],.marked⟩
theorem checked790:cell790.check OrdinaryBooks.middle 342:=by decide +kernel
def cell791:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,4097,some 8192,771221,[],.marked⟩
theorem checked791:cell791.check OrdinaryBooks.middle 342:=by decide +kernel
def cell792:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,2049,some 4096,771221,[],.marked⟩
theorem checked792:cell792.check OrdinaryBooks.middle 342:=by decide +kernel
def cell793:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,1537,some 2048,771221,[],.marked⟩
theorem checked793:cell793.check OrdinaryBooks.middle 342:=by decide +kernel
def cell794:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,1025,some 1536,771221,[OrdSource.row271],.marked⟩
theorem checked794:cell794.check OrdinaryBooks.middle 342:=by decide +kernel
def cell795:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,513,some 1024,771221,[OrdSource.row270],.marked⟩
theorem checked795:cell795.check OrdinaryBooks.middle 342:=by decide +kernel
def cell796:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,257,some 512,771221,[OrdSource.row269],.marked⟩
theorem checked796:cell796.check OrdinaryBooks.middle 342:=by decide +kernel
def cell797:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,161,some 256,771221,[OrdSource.row268],.marked⟩
theorem checked797:cell797.check OrdinaryBooks.middle 342:=by decide +kernel
def cell798:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,97,some 160,771221,[OrdSource.row267],.marked⟩
theorem checked798:cell798.check OrdinaryBooks.middle 342:=by decide +kernel
def cell799:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,65,some 96,771221,[OrdSource.row266],.marked⟩
theorem checked799:cell799.check OrdinaryBooks.middle 342:=by decide +kernel
def cell800:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,48,some 64,771221,[OrdSource.row265],.marked⟩
theorem checked800:cell800.check OrdinaryBooks.middle 342:=by decide +kernel
def cell801:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,36,some 47,771221,[OrdSource.row264],.marked⟩
theorem checked801:cell801.check OrdinaryBooks.middle 342:=by decide +kernel
def cell802:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,27,some 35,771221,[OrdSource.row263],.marked⟩
theorem checked802:cell802.check OrdinaryBooks.middle 342:=by decide +kernel
def cell803:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,21,some 26,771221,[OrdSource.row262],.marked⟩
theorem checked803:cell803.check OrdinaryBooks.middle 342:=by decide +kernel
def cell804:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,15,some 20,771221,[OrdSource.row261],.marked⟩
theorem checked804:cell804.check OrdinaryBooks.middle 342:=by decide +kernel
def cell805:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,10,some 14,771221,[OrdSource.row260],.marked⟩
theorem checked805:cell805.check OrdinaryBooks.middle 342:=by decide +kernel
def cell806:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,6,some 9,771221,[OrdSource.row259],.marked⟩
theorem checked806:cell806.check OrdinaryBooks.middle 342:=by decide +kernel
def cell807:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,3,some 5,771221,[OrdSource.row258],.surface⟩
theorem checked807:cell807.check OrdinaryBooks.middle 342:=by decide +kernel
def cell808:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,1,some 2,771221,[OrdSource.row257],.surface⟩
theorem checked808:cell808.check OrdinaryBooks.middle 342:=by decide +kernel
def cell809:OrdinaryCell.Row 2390 2534:=⟨22,22,9,6,0,some 0,771221,[],.ambient⟩
theorem checked809:cell809.check OrdinaryBooks.middle 342:=by decide +kernel
def cell810:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,32769,none,128536,[OrdSource.row150],.excluded⟩
theorem checked810:cell810.check OrdinaryBooks.middle 342:=by decide +kernel
def cell811:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,16385,some 32768,128536,[OrdSource.row149],.excluded⟩
theorem checked811:cell811.check OrdinaryBooks.middle 342:=by decide +kernel
def cell812:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,8193,some 16384,128536,[OrdSource.row148],.excluded⟩
theorem checked812:cell812.check OrdinaryBooks.middle 342:=by decide +kernel
def cell813:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,4097,some 8192,128536,[OrdSource.row147],.excluded⟩
theorem checked813:cell813.check OrdinaryBooks.middle 342:=by decide +kernel
def cell814:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,2049,some 4096,128536,[OrdSource.row146],.excluded⟩
theorem checked814:cell814.check OrdinaryBooks.middle 342:=by decide +kernel
def cell815:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,1025,some 2048,128536,[OrdSource.row145],.excluded⟩
theorem checked815:cell815.check OrdinaryBooks.middle 342:=by decide +kernel
def cell816:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,513,some 1024,128536,[OrdSource.row143,OrdSource.row144],.excluded⟩
theorem checked816:cell816.check OrdinaryBooks.middle 342:=by decide +kernel
def cell817:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,257,some 512,128536,[OrdSource.row142],.marked⟩
theorem checked817:cell817.check OrdinaryBooks.middle 342:=by decide +kernel
def cell818:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,161,some 256,128536,[OrdSource.row141],.marked⟩
theorem checked818:cell818.check OrdinaryBooks.middle 342:=by decide +kernel
def cell819:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,97,some 160,128536,[OrdSource.row140],.marked⟩
theorem checked819:cell819.check OrdinaryBooks.middle 342:=by decide +kernel
def cell820:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,65,some 96,128536,[OrdSource.row139],.marked⟩
theorem checked820:cell820.check OrdinaryBooks.middle 342:=by decide +kernel
def cell821:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,48,some 64,128536,[OrdSource.row138],.affine⟩
theorem checked821:cell821.check OrdinaryBooks.middle 342:=by decide +kernel
def cell822:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,36,some 47,128536,[OrdSource.row136],.affine⟩
theorem checked822:cell822.check OrdinaryBooks.middle 342:=by decide +kernel
def cell823:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,27,some 35,128536,[],.affine⟩
theorem checked823:cell823.check OrdinaryBooks.middle 342:=by decide +kernel
def cell824:OrdinaryCell.Row 2390 2534:=⟨23,24,9,1,21,some 26,128536,[],.affine⟩
theorem checked824:cell824.check OrdinaryBooks.middle 342:=by decide +kernel
end Research6969.OrdReceipts
end Z6969Source1714

-- Source: Research6969.OrdRouteMiddle0
section Z6969Source1715
set_option autoImplicit true
namespace Research6969.OrdRouteMiddle0
open OrdinaryRoute
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000
private theorem leaf0:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,32769,none⟩:=
  plain OrdReceipts.cell681 OrdReceipts.checked681 (by decide) (by decide)
private theorem leaf1:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,16385,some 32768⟩:=
  plain OrdReceipts.cell682 OrdReceipts.checked682 (by decide) (by decide)
private theorem leaf2:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,8193,some 16384⟩:=
  plain OrdReceipts.cell683 OrdReceipts.checked683 (by decide) (by decide)
private theorem leaf3:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,4097,some 8192⟩:=
  plain OrdReceipts.cell684 OrdReceipts.checked684 (by decide) (by decide)
private theorem leaf4:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,2049,some 4096⟩:=
  plain OrdReceipts.cell685 OrdReceipts.checked685 (by decide) (by decide)
private theorem leaf5:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,1025,some 2048⟩:=
  plain OrdReceipts.cell686 OrdReceipts.checked686 (by decide) (by decide)
private theorem leaf6:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,513,some 1024⟩:=
  plain OrdReceipts.cell687 OrdReceipts.checked687 (by decide) (by decide)
private theorem leaf7:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,257,some 512⟩:=
  plain OrdReceipts.cell688 OrdReceipts.checked688 (by decide) (by decide)
private theorem leaf8:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,161,some 256⟩:=
  plain OrdReceipts.cell689 OrdReceipts.checked689 (by decide) (by decide)
private theorem leaf9:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,97,some 160⟩:=
  plain OrdReceipts.cell690 OrdReceipts.checked690 (by decide) (by decide)
private theorem leaf10:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,65,some 96⟩:=
  plain OrdReceipts.cell691 OrdReceipts.checked691 (by decide) (by decide)
private theorem leaf11:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,48,some 64⟩:=
  plain OrdReceipts.cell692 OrdReceipts.checked692 (by decide) (by decide)
private theorem leaf12:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,36,some 47⟩:=
  plain OrdReceipts.cell693 OrdReceipts.checked693 (by decide) (by decide)
private theorem leaf13:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,27,some 35⟩:=
  plain OrdReceipts.cell694 OrdReceipts.checked694 (by decide) (by decide)
private theorem leaf14:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,21,some 26⟩:=
  plain OrdReceipts.cell695 OrdReceipts.checked695 (by decide) (by decide)
private theorem leaf15:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,15,some 20⟩:=
  plain OrdReceipts.cell696 OrdReceipts.checked696 (by decide) (by decide)
private theorem leaf16:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,10,some 14⟩:=
  plain OrdReceipts.cell697 OrdReceipts.checked697 (by decide) (by decide)
private theorem leaf17:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,6,some 9⟩:=
  plain OrdReceipts.cell698 OrdReceipts.checked698 (by decide) (by decide)
private theorem leaf18:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,3,some 5⟩:=
  plain OrdReceipts.cell699 OrdReceipts.checked699 (by decide) (by decide)
private theorem leaf19:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,1,some 2⟩:=
  plain OrdReceipts.cell700 OrdReceipts.checked700 (by decide) (by decide)
private theorem leaf20:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,1,0,some 0⟩:=
  plain OrdReceipts.cell701 OrdReceipts.checked701 (by decide) (by decide)
private theorem leaf21:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,32769,none⟩:=
  plain OrdReceipts.cell702 OrdReceipts.checked702 (by decide) (by decide)
private theorem leaf22:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,16385,some 32768⟩:=
  plain OrdReceipts.cell703 OrdReceipts.checked703 (by decide) (by decide)
private theorem leaf23:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,8193,some 16384⟩:=
  plain OrdReceipts.cell704 OrdReceipts.checked704 (by decide) (by decide)
private theorem leaf24:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,4097,some 8192⟩:=
  plain OrdReceipts.cell705 OrdReceipts.checked705 (by decide) (by decide)
private theorem leaf25:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,2049,some 4096⟩:=
  plain OrdReceipts.cell706 OrdReceipts.checked706 (by decide) (by decide)
private theorem leaf26:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,1025,some 2048⟩:=
  plain OrdReceipts.cell707 OrdReceipts.checked707 (by decide) (by decide)
private theorem leaf27:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,513,some 1024⟩:=
  plain OrdReceipts.cell708 OrdReceipts.checked708 (by decide) (by decide)
private theorem leaf28:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,257,some 512⟩:=
  plain OrdReceipts.cell709 OrdReceipts.checked709 (by decide) (by decide)
private theorem leaf29:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,161,some 256⟩:=
  plain OrdReceipts.cell710 OrdReceipts.checked710 (by decide) (by decide)
private theorem leaf30:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,97,some 160⟩:=
  plain OrdReceipts.cell711 OrdReceipts.checked711 (by decide) (by decide)
private theorem leaf31:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,65,some 96⟩:=
  plain OrdReceipts.cell712 OrdReceipts.checked712 (by decide) (by decide)
private theorem leaf32:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,48,some 64⟩:=
  plain OrdReceipts.cell713 OrdReceipts.checked713 (by decide) (by decide)
private theorem leaf33:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,36,some 47⟩:=
  plain OrdReceipts.cell714 OrdReceipts.checked714 (by decide) (by decide)
private theorem leaf34:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,27,some 35⟩:=
  plain OrdReceipts.cell715 OrdReceipts.checked715 (by decide) (by decide)
private theorem leaf35:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,21,some 26⟩:=
  plain OrdReceipts.cell716 OrdReceipts.checked716 (by decide) (by decide)
private theorem leaf36:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,15,some 20⟩:=
  plain OrdReceipts.cell717 OrdReceipts.checked717 (by decide) (by decide)
private theorem leaf37:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,10,some 14⟩:=
  plain OrdReceipts.cell718 OrdReceipts.checked718 (by decide) (by decide)
private theorem leaf38:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,6,some 9⟩:=
  plain OrdReceipts.cell719 OrdReceipts.checked719 (by decide) (by decide)
private theorem leaf39:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,3,some 5⟩:=
  plain OrdReceipts.cell720 OrdReceipts.checked720 (by decide) (by decide)
private theorem leaf40:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,1,some 2⟩:=
  plain OrdReceipts.cell721 OrdReceipts.checked721 (by decide) (by decide)
private theorem leaf41:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,2,0,some 0⟩:=
  plain OrdReceipts.cell722 OrdReceipts.checked722 (by decide) (by decide)
private theorem leaf42:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,32769,none⟩:=
  plain OrdReceipts.cell723 OrdReceipts.checked723 (by decide) (by decide)
private theorem leaf43:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,16385,some 32768⟩:=
  plain OrdReceipts.cell724 OrdReceipts.checked724 (by decide) (by decide)
private theorem leaf44:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,8193,some 16384⟩:=
  plain OrdReceipts.cell725 OrdReceipts.checked725 (by decide) (by decide)
private theorem leaf45:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,4097,some 8192⟩:=
  plain OrdReceipts.cell726 OrdReceipts.checked726 (by decide) (by decide)
private theorem leaf46:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,2049,some 4096⟩:=
  plain OrdReceipts.cell727 OrdReceipts.checked727 (by decide) (by decide)
private theorem leaf47:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,1025,some 2048⟩:=
  plain OrdReceipts.cell728 OrdReceipts.checked728 (by decide) (by decide)
private theorem leaf48:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,513,some 1024⟩:=
  plain OrdReceipts.cell729 OrdReceipts.checked729 (by decide) (by decide)
private theorem leaf49:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,257,some 512⟩:=
  plain OrdReceipts.cell730 OrdReceipts.checked730 (by decide) (by decide)
private theorem leaf50:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,161,some 256⟩:=
  plain OrdReceipts.cell731 OrdReceipts.checked731 (by decide) (by decide)
private theorem leaf51:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,97,some 160⟩:=
  plain OrdReceipts.cell732 OrdReceipts.checked732 (by decide) (by decide)
private theorem leaf52:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,65,some 96⟩:=
  plain OrdReceipts.cell733 OrdReceipts.checked733 (by decide) (by decide)
private theorem leaf53:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,48,some 64⟩:=
  plain OrdReceipts.cell734 OrdReceipts.checked734 (by decide) (by decide)
private theorem leaf54:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,36,some 47⟩:=
  plain OrdReceipts.cell735 OrdReceipts.checked735 (by decide) (by decide)
private theorem leaf55:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,27,some 35⟩:=
  plain OrdReceipts.cell736 OrdReceipts.checked736 (by decide) (by decide)
private theorem leaf56:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,21,some 26⟩:=
  plain OrdReceipts.cell737 OrdReceipts.checked737 (by decide) (by decide)
private theorem leaf57:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,15,some 20⟩:=
  plain OrdReceipts.cell738 OrdReceipts.checked738 (by decide) (by decide)
private theorem leaf58:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,13,some 14⟩:=
  plain OrdReceipts.cell739 OrdReceipts.checked739 (by decide) (by decide)
private theorem leaf59:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,10,some 12⟩:=
  plain OrdReceipts.cell740 OrdReceipts.checked740 (by decide) (by decide)
private theorem leaf60:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,6,some 9⟩:=
  plain OrdReceipts.cell741 OrdReceipts.checked741 (by decide) (by decide)
private theorem leaf61:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,3,some 5⟩:=
  plain OrdReceipts.cell742 OrdReceipts.checked742 (by decide) (by decide)
private theorem leaf62:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,1,some 2⟩:=
  plain OrdReceipts.cell743 OrdReceipts.checked743 (by decide) (by decide)
private theorem leaf63:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,3,0,some 0⟩:=
  plain OrdReceipts.cell744 OrdReceipts.checked744 (by decide) (by decide)
private theorem leaf64:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,32769,none⟩:=
  plain OrdReceipts.cell745 OrdReceipts.checked745 (by decide) (by decide)
private theorem leaf65:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,16385,some 32768⟩:=
  plain OrdReceipts.cell746 OrdReceipts.checked746 (by decide) (by decide)
private theorem leaf66:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,8193,some 16384⟩:=
  plain OrdReceipts.cell747 OrdReceipts.checked747 (by decide) (by decide)
private theorem leaf67:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,4097,some 8192⟩:=
  plain OrdReceipts.cell748 OrdReceipts.checked748 (by decide) (by decide)
private theorem leaf68:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,2049,some 4096⟩:=
  plain OrdReceipts.cell749 OrdReceipts.checked749 (by decide) (by decide)
private theorem leaf69:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,1025,some 2048⟩:=
  plain OrdReceipts.cell750 OrdReceipts.checked750 (by decide) (by decide)
private theorem leaf70:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,513,some 1024⟩:=
  plain OrdReceipts.cell751 OrdReceipts.checked751 (by decide) (by decide)
private theorem leaf71:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,257,some 512⟩:=
  plain OrdReceipts.cell752 OrdReceipts.checked752 (by decide) (by decide)
private theorem leaf72:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,161,some 256⟩:=
  plain OrdReceipts.cell753 OrdReceipts.checked753 (by decide) (by decide)
private theorem leaf73:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,97,some 160⟩:=
  plain OrdReceipts.cell754 OrdReceipts.checked754 (by decide) (by decide)
private theorem leaf74:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,65,some 96⟩:=
  plain OrdReceipts.cell755 OrdReceipts.checked755 (by decide) (by decide)
private theorem leaf75:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,48,some 64⟩:=
  plain OrdReceipts.cell756 OrdReceipts.checked756 (by decide) (by decide)
private theorem leaf76:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,36,some 47⟩:=
  plain OrdReceipts.cell757 OrdReceipts.checked757 (by decide) (by decide)
private theorem leaf77:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,27,some 35⟩:=
  plain OrdReceipts.cell758 OrdReceipts.checked758 (by decide) (by decide)
private theorem leaf78:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,21,some 26⟩:=
  plain OrdReceipts.cell759 OrdReceipts.checked759 (by decide) (by decide)
private theorem leaf79:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,15,some 20⟩:=
  plain OrdReceipts.cell760 OrdReceipts.checked760 (by decide) (by decide)
private theorem leaf80:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,10,some 14⟩:=
  plain OrdReceipts.cell761 OrdReceipts.checked761 (by decide) (by decide)
private theorem leaf81:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,6,some 9⟩:=
  plain OrdReceipts.cell762 OrdReceipts.checked762 (by decide) (by decide)
private theorem leaf82:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,3,some 5⟩:=
  plain OrdReceipts.cell763 OrdReceipts.checked763 (by decide) (by decide)
private theorem leaf83:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,1,some 2⟩:=
  plain OrdReceipts.cell764 OrdReceipts.checked764 (by decide) (by decide)
private theorem leaf84:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,4,0,some 0⟩:=
  plain OrdReceipts.cell765 OrdReceipts.checked765 (by decide) (by decide)
private theorem leaf85:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,32769,none⟩:=
  plain OrdReceipts.cell766 OrdReceipts.checked766 (by decide) (by decide)
private theorem leaf86:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,16385,some 32768⟩:=
  plain OrdReceipts.cell767 OrdReceipts.checked767 (by decide) (by decide)
private theorem leaf87:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,8193,some 16384⟩:=
  plain OrdReceipts.cell768 OrdReceipts.checked768 (by decide) (by decide)
private theorem leaf88:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,4097,some 8192⟩:=
  plain OrdReceipts.cell769 OrdReceipts.checked769 (by decide) (by decide)
private theorem leaf89:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,2049,some 4096⟩:=
  plain OrdReceipts.cell770 OrdReceipts.checked770 (by decide) (by decide)
private theorem leaf90:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,1537,some 2048⟩:=
  plain OrdReceipts.cell771 OrdReceipts.checked771 (by decide) (by decide)
private theorem leaf91:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,1025,some 1536⟩:=
  plain OrdReceipts.cell772 OrdReceipts.checked772 (by decide) (by decide)
private theorem leaf92:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,513,some 1024⟩:=
  plain OrdReceipts.cell773 OrdReceipts.checked773 (by decide) (by decide)
private theorem leaf93:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,257,some 512⟩:=
  plain OrdReceipts.cell774 OrdReceipts.checked774 (by decide) (by decide)
private theorem leaf94:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,161,some 256⟩:=
  plain OrdReceipts.cell775 OrdReceipts.checked775 (by decide) (by decide)
private theorem leaf95:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,97,some 160⟩:=
  plain OrdReceipts.cell776 OrdReceipts.checked776 (by decide) (by decide)
private theorem leaf96:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,65,some 96⟩:=
  plain OrdReceipts.cell777 OrdReceipts.checked777 (by decide) (by decide)
private theorem leaf97:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,48,some 64⟩:=
  plain OrdReceipts.cell778 OrdReceipts.checked778 (by decide) (by decide)
private theorem leaf98:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,36,some 47⟩:=
  plain OrdReceipts.cell779 OrdReceipts.checked779 (by decide) (by decide)
private theorem leaf99:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,27,some 35⟩:=
  plain OrdReceipts.cell780 OrdReceipts.checked780 (by decide) (by decide)
private theorem leaf100:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,21,some 26⟩:=
  plain OrdReceipts.cell781 OrdReceipts.checked781 (by decide) (by decide)
private theorem leaf101:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,15,some 20⟩:=
  plain OrdReceipts.cell782 OrdReceipts.checked782 (by decide) (by decide)
private theorem leaf102:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,10,some 14⟩:=
  plain OrdReceipts.cell783 OrdReceipts.checked783 (by decide) (by decide)
private theorem leaf103:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,6,some 9⟩:=
  plain OrdReceipts.cell784 OrdReceipts.checked784 (by decide) (by decide)
private theorem leaf104:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,3,some 5⟩:=
  plain OrdReceipts.cell785 OrdReceipts.checked785 (by decide) (by decide)
private theorem leaf105:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,1,some 2⟩:=
  plain OrdReceipts.cell786 OrdReceipts.checked786 (by decide) (by decide)
private theorem leaf106:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,5,0,some 0⟩:=
  plain OrdReceipts.cell787 OrdReceipts.checked787 (by decide) (by decide)
private theorem leaf107:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,32769,none⟩:=
  plain OrdReceipts.cell788 OrdReceipts.checked788 (by decide) (by decide)
private theorem leaf108:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,16385,some 32768⟩:=
  plain OrdReceipts.cell789 OrdReceipts.checked789 (by decide) (by decide)
private theorem leaf109:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,8193,some 16384⟩:=
  plain OrdReceipts.cell790 OrdReceipts.checked790 (by decide) (by decide)
private theorem leaf110:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,4097,some 8192⟩:=
  plain OrdReceipts.cell791 OrdReceipts.checked791 (by decide) (by decide)
private theorem leaf111:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,2049,some 4096⟩:=
  plain OrdReceipts.cell792 OrdReceipts.checked792 (by decide) (by decide)
private theorem leaf112:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,1537,some 2048⟩:=
  plain OrdReceipts.cell793 OrdReceipts.checked793 (by decide) (by decide)
private theorem leaf113:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,1025,some 1536⟩:=
  plain OrdReceipts.cell794 OrdReceipts.checked794 (by decide) (by decide)
private theorem leaf114:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,513,some 1024⟩:=
  plain OrdReceipts.cell795 OrdReceipts.checked795 (by decide) (by decide)
private theorem leaf115:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,257,some 512⟩:=
  plain OrdReceipts.cell796 OrdReceipts.checked796 (by decide) (by decide)
private theorem leaf116:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,161,some 256⟩:=
  plain OrdReceipts.cell797 OrdReceipts.checked797 (by decide) (by decide)
private theorem leaf117:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,97,some 160⟩:=
  plain OrdReceipts.cell798 OrdReceipts.checked798 (by decide) (by decide)
private theorem leaf118:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,65,some 96⟩:=
  plain OrdReceipts.cell799 OrdReceipts.checked799 (by decide) (by decide)
private theorem leaf119:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,48,some 64⟩:=
  plain OrdReceipts.cell800 OrdReceipts.checked800 (by decide) (by decide)
private theorem leaf120:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,36,some 47⟩:=
  plain OrdReceipts.cell801 OrdReceipts.checked801 (by decide) (by decide)
private theorem leaf121:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,27,some 35⟩:=
  plain OrdReceipts.cell802 OrdReceipts.checked802 (by decide) (by decide)
private theorem leaf122:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,21,some 26⟩:=
  plain OrdReceipts.cell803 OrdReceipts.checked803 (by decide) (by decide)
private theorem leaf123:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,15,some 20⟩:=
  plain OrdReceipts.cell804 OrdReceipts.checked804 (by decide) (by decide)
private theorem leaf124:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,10,some 14⟩:=
  plain OrdReceipts.cell805 OrdReceipts.checked805 (by decide) (by decide)
private theorem leaf125:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,6,some 9⟩:=
  plain OrdReceipts.cell806 OrdReceipts.checked806 (by decide) (by decide)
private theorem leaf126:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,3,some 5⟩:=
  plain OrdReceipts.cell807 OrdReceipts.checked807 (by decide) (by decide)
private theorem leaf127:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,1,some 2⟩:=
  plain OrdReceipts.cell808 OrdReceipts.checked808 (by decide) (by decide)
private theorem leaf128:Done 2390 2534 OrdinaryBooks.middle 342 ⟨22,22,9,6,0,some 0⟩:=
  plain OrdReceipts.cell809 OrdReceipts.checked809 (by decide) (by decide)
private theorem tail1_32769:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 32769:=leaf0
private theorem tail1_16385:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 16385:=join leaf1 tail1_32769
private theorem tail1_8193:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 8193:=join leaf2 tail1_16385
private theorem tail1_4097:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 4097:=join leaf3 tail1_8193
private theorem tail1_2049:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 2049:=join leaf4 tail1_4097
private theorem tail1_1025:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 1025:=join leaf5 tail1_2049
private theorem tail1_513:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 513:=join leaf6 tail1_1025
private theorem tail1_257:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 257:=join leaf7 tail1_513
private theorem tail1_161:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 161:=join leaf8 tail1_257
private theorem tail1_97:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 97:=join leaf9 tail1_161
private theorem tail1_65:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 65:=join leaf10 tail1_97
private theorem tail1_48:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 48:=join leaf11 tail1_65
private theorem tail1_36:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 36:=join leaf12 tail1_48
private theorem tail1_27:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 27:=join leaf13 tail1_36
private theorem tail1_21:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 21:=join leaf14 tail1_27
private theorem tail1_15:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 15:=join leaf15 tail1_21
private theorem tail1_10:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 10:=join leaf16 tail1_15
private theorem tail1_6:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 6:=join leaf17 tail1_10
private theorem tail1_3:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 3:=join leaf18 tail1_6
private theorem tail1_1:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 1:=join leaf19 tail1_3
private theorem tail1_0:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 1 0:=join leaf20 tail1_1
private theorem tail2_32769:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 32769:=leaf21
private theorem tail2_16385:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 16385:=join leaf22 tail2_32769
private theorem tail2_8193:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 8193:=join leaf23 tail2_16385
private theorem tail2_4097:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 4097:=join leaf24 tail2_8193
private theorem tail2_2049:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 2049:=join leaf25 tail2_4097
private theorem tail2_1025:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 1025:=join leaf26 tail2_2049
private theorem tail2_513:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 513:=join leaf27 tail2_1025
private theorem tail2_257:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 257:=join leaf28 tail2_513
private theorem tail2_161:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 161:=join leaf29 tail2_257
private theorem tail2_97:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 97:=join leaf30 tail2_161
private theorem tail2_65:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 65:=join leaf31 tail2_97
private theorem tail2_48:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 48:=join leaf32 tail2_65
private theorem tail2_36:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 36:=join leaf33 tail2_48
private theorem tail2_27:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 27:=join leaf34 tail2_36
private theorem tail2_21:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 21:=join leaf35 tail2_27
private theorem tail2_15:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 15:=join leaf36 tail2_21
private theorem tail2_10:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 10:=join leaf37 tail2_15
private theorem tail2_6:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 6:=join leaf38 tail2_10
private theorem tail2_3:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 3:=join leaf39 tail2_6
private theorem tail2_1:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 1:=join leaf40 tail2_3
private theorem tail2_0:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 2 0:=join leaf41 tail2_1
private theorem tail3_32769:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 32769:=leaf42
private theorem tail3_16385:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 16385:=join leaf43 tail3_32769
private theorem tail3_8193:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 8193:=join leaf44 tail3_16385
private theorem tail3_4097:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 4097:=join leaf45 tail3_8193
private theorem tail3_2049:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 2049:=join leaf46 tail3_4097
private theorem tail3_1025:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 1025:=join leaf47 tail3_2049
private theorem tail3_513:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 513:=join leaf48 tail3_1025
private theorem tail3_257:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 257:=join leaf49 tail3_513
private theorem tail3_161:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 161:=join leaf50 tail3_257
private theorem tail3_97:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 97:=join leaf51 tail3_161
private theorem tail3_65:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 65:=join leaf52 tail3_97
private theorem tail3_48:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 48:=join leaf53 tail3_65
private theorem tail3_36:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 36:=join leaf54 tail3_48
private theorem tail3_27:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 27:=join leaf55 tail3_36
private theorem tail3_21:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 21:=join leaf56 tail3_27
private theorem tail3_15:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 15:=join leaf57 tail3_21
private theorem tail3_13:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 13:=join leaf58 tail3_15
private theorem tail3_10:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 10:=join leaf59 tail3_13
private theorem tail3_6:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 6:=join leaf60 tail3_10
private theorem tail3_3:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 3:=join leaf61 tail3_6
private theorem tail3_1:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 1:=join leaf62 tail3_3
private theorem tail3_0:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 3 0:=join leaf63 tail3_1
private theorem tail4_32769:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 32769:=leaf64
private theorem tail4_16385:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 16385:=join leaf65 tail4_32769
private theorem tail4_8193:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 8193:=join leaf66 tail4_16385
private theorem tail4_4097:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 4097:=join leaf67 tail4_8193
private theorem tail4_2049:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 2049:=join leaf68 tail4_4097
private theorem tail4_1025:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 1025:=join leaf69 tail4_2049
private theorem tail4_513:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 513:=join leaf70 tail4_1025
private theorem tail4_257:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 257:=join leaf71 tail4_513
private theorem tail4_161:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 161:=join leaf72 tail4_257
private theorem tail4_97:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 97:=join leaf73 tail4_161
private theorem tail4_65:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 65:=join leaf74 tail4_97
private theorem tail4_48:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 48:=join leaf75 tail4_65
private theorem tail4_36:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 36:=join leaf76 tail4_48
private theorem tail4_27:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 27:=join leaf77 tail4_36
private theorem tail4_21:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 21:=join leaf78 tail4_27
private theorem tail4_15:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 15:=join leaf79 tail4_21
private theorem tail4_10:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 10:=join leaf80 tail4_15
private theorem tail4_6:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 6:=join leaf81 tail4_10
private theorem tail4_3:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 3:=join leaf82 tail4_6
private theorem tail4_1:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 1:=join leaf83 tail4_3
private theorem tail4_0:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 4 0:=join leaf84 tail4_1
private theorem tail5_32769:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 32769:=leaf85
private theorem tail5_16385:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 16385:=join leaf86 tail5_32769
private theorem tail5_8193:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 8193:=join leaf87 tail5_16385
private theorem tail5_4097:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 4097:=join leaf88 tail5_8193
private theorem tail5_2049:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 2049:=join leaf89 tail5_4097
private theorem tail5_1537:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 1537:=join leaf90 tail5_2049
private theorem tail5_1025:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 1025:=join leaf91 tail5_1537
private theorem tail5_513:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 513:=join leaf92 tail5_1025
private theorem tail5_257:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 257:=join leaf93 tail5_513
private theorem tail5_161:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 161:=join leaf94 tail5_257
private theorem tail5_97:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 97:=join leaf95 tail5_161
private theorem tail5_65:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 65:=join leaf96 tail5_97
private theorem tail5_48:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 48:=join leaf97 tail5_65
private theorem tail5_36:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 36:=join leaf98 tail5_48
private theorem tail5_27:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 27:=join leaf99 tail5_36
private theorem tail5_21:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 21:=join leaf100 tail5_27
private theorem tail5_15:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 15:=join leaf101 tail5_21
private theorem tail5_10:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 10:=join leaf102 tail5_15
private theorem tail5_6:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 6:=join leaf103 tail5_10
private theorem tail5_3:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 3:=join leaf104 tail5_6
private theorem tail5_1:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 1:=join leaf105 tail5_3
private theorem tail5_0:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 5 0:=join leaf106 tail5_1
private theorem tail6_32769:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 32769:=leaf107
private theorem tail6_16385:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 16385:=join leaf108 tail6_32769
private theorem tail6_8193:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 8193:=join leaf109 tail6_16385
private theorem tail6_4097:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 4097:=join leaf110 tail6_8193
private theorem tail6_2049:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 2049:=join leaf111 tail6_4097
private theorem tail6_1537:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 1537:=join leaf112 tail6_2049
private theorem tail6_1025:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 1025:=join leaf113 tail6_1537
private theorem tail6_513:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 513:=join leaf114 tail6_1025
private theorem tail6_257:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 257:=join leaf115 tail6_513
private theorem tail6_161:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 161:=join leaf116 tail6_257
private theorem tail6_97:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 97:=join leaf117 tail6_161
private theorem tail6_65:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 65:=join leaf118 tail6_97
private theorem tail6_48:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 48:=join leaf119 tail6_65
private theorem tail6_36:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 36:=join leaf120 tail6_48
private theorem tail6_27:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 27:=join leaf121 tail6_36
private theorem tail6_21:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 21:=join leaf122 tail6_27
private theorem tail6_15:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 15:=join leaf123 tail6_21
private theorem tail6_10:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 10:=join leaf124 tail6_15
private theorem tail6_6:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 6:=join leaf125 tail6_10
private theorem tail6_3:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 3:=join leaf126 tail6_6
private theorem tail6_1:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 1:=join leaf127 tail6_3
private theorem tail6_0:Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 6 0:=join leaf128 tail6_1
theorem allDegrees (a:ℕ) (lo:0<a) (hi:a≤6):
    Tail 2390 2534 OrdinaryBooks.middle 342 22 22 9 a 0:=by
  interval_cases a
  · exact tail1_0
  · exact tail2_0
  · exact tail3_0
  · exact tail4_0
  · exact tail5_0
  · exact tail6_0
end Research6969.OrdRouteMiddle0
end Z6969Source1715

end Merged_Z6969Pack0720
