import ProximityPrize.SubmissionLower.R6960Low6960Inventory
import ProximityPrize.SubmissionLower.Final50FatReserve

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Lower6960.Low
open Finset
open K1_13 (Shape chart ceilDiv mixed32 shape)
open K1_13_8 (Valid)
open P3_6 (commonBox resultantBox)
open Final50FatReserve (degreeCap)
open K1_13_8_4 (TotalLE)
open scoped BigOperators Classical

abbrev errors : ℕ := 262144-agreement
abbrev incidenceGap : ℕ := agreement-physicalDegree
abbrev taylorLength : ℕ := physicalDegree+1
abbrev fatOrder : ℕ := 43848
abbrev divisorOrder : ℕ := 39890
abbrev isolatedOrder : ℕ := 430

def linearChart (p : Shape) : Shape :=
  let i := 3 + taylorLength * (p.j - 2)
  ⟨max (1 + taylorLength * (p.b - 1)) i, i, min (taylorLength + 1) (i / 3)⟩
def fatPrice (x : Shape) : ℕ :=
  let p := x.chamber
  let h := if x.t = 1 then linearChart p else chart (taylorLength + 4) p
  let q : Shape := resultantBox
  let big : Shape := ⟨commonBox.b + q.b / divisorOrder, commonBox.j + q.j / divisorOrder, 0⟩
  let cut : Shape := ⟨max (max h.b big.b) (max h.j (big.j + 1)),
    max h.j (big.j + 1), max 1 h.t⟩
  let divisors := ceilDiv (errors * mixed32 p big cut h) (32 * incidenceGap) +
    ceilDiv (mixed32 p big cut p) 32 + 20 * p.b * h.b^2 + 5 * physicalDegree * p.b * h.b + 1
  let singular := if 1 < x.t then ceilDiv (4 * x.t * mixed32 p p h h) 32 + x.t * x.b^2 + 1 else 0
  let curveLength := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  let curves := ceilDiv (errors * mixed32 p q q h + incidenceGap * mixed32 p q q p)
    (32 * incidenceGap * curveLength)
  let isolated := ceilDiv (3 * q.j^2 * (2 * q.b - q.j)) (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
  divisors + singular + curves + isolated

/-- Each entry pays the fat factors at the actual retained total width.
The two-factor alternatives use every valid split of that same width. -/
def retainedTariffs : ℕ→ℕ→List ℕ
  | 3,1 => [0, 3200987024399067, 3200987024399067, 3200987024399067, 3688474415310012, 4183259089080658, 4687476833083003, 5203263434689048, 5732754681270794, 6278086360200239, 6841394258849385, 7424814164590230, 8030481864794775, 8660533146835020, 9317103798082967, 10002329605910612, 10718346357689957, 11467289840793002, 12251295842591748, 13072500150458194, 13933038551764339, 14835046833882184, 15780660784183729, 16772016190040975, 17811248838825920, 18900494517910566]
  | 4,1 => [0, 0, 7382522999922226, 7382522999922226, 7382522999922226, 8594286492576102, 9815483055461680, 11048248475950958, 12294718541415935, 13557029039228613, 14837315756760991, 16137714481385068, 17460361000472846, 18807391101396322, 20180940571527500, 21583145198238378, 23016140768900955, 24482063070887233, 25983047891569211, 27521231018318888, 29098748238508265, 30717735339509342, 32380328108694120, 34088662333434598]
  | 5,1 => [0, 0, 15599627679064809, 15599627679064809, 15599627679064809, 15599627679064809, 17856402056721273, 20124745291981436, 22406793172217299, 24704681484800863, 27020546017104126, 29356522556499090, 31714746890357753, 34097354806052116, 36506482090954181, 38944264532435944, 41412837917869407, 43914338034626571, 46450900670079434, 49024661611599997, 51637756646560261]
  | 6,1 => [0, 0, 26966888123638774, 26966888123638774, 26966888123638774, 26966888123638774, 26966888123638774, 30191034469437675, 33428885460212276, 36682576883334578, 39954244526176579, 43246024176110281, 46560051620507682, 49898462646740783, 53263393042181584, 56656978594202086, 60081355090174287]
  | 7,1 => [0, 0, 0, 41676256637920564, 41676256637920564, 41676256637920564, 41676256637920564, 41676256637920564, 45869910739233903, 50079405272894942, 54306876026275681]
  | 6,2 => [0, 0, 87483289404580951, 87483289404580961, 87483289404580975, 87483289404580993, 87483289404581015, 99698781084988573, 111968738617312733, 124301705663343579, 136706225884871188, 149190842943685642, 161764100501577018, 174434542220335400, 187210711761750865, 200101152787613494, 213114408959713367]
  | 7,2 => [0, 0, 0, 157890651360317645, 157890651360317659, 157890651360317677, 157890651360317699, 157890651360317725, 176404816449836122, 194981991053061202, 213630718831783047]
  | _,_ => []

def retainedTariff (b j t : ℕ) : ℕ := (retainedTariffs j t).getD b 0

def singleTariffs : ℕ→ℕ→List ℕ
  | 3,1 => [0, 3200987024399067, 3200987024399067, 3200987024399067, 3688474415310012, 4183259089080658, 4687476833083003, 5203263434689048, 5732754681270794, 6278086360200239, 6841394258849385, 7424814164590230, 8030481864794775, 8660533146835020, 9317103798082967, 10002329605910612, 10718346357689957, 11467289840793002, 12251295842591748, 13072500150458194, 13933038551764339, 14835046833882184, 15780660784183729, 16772016190040975, 17811248838825920, 18900494517910566]
  | 4,1 => [0, 0, 7382522999922226, 7382522999922226, 7382522999922226, 8594286492576102, 9815483055461680, 11048248475950958, 12294718541415935, 13557029039228613, 14837315756760991, 16137714481385068, 17460361000472846, 18807391101396322, 20180940571527500, 21583145198238378, 23016140768900955, 24482063070887233, 25983047891569211, 27521231018318888, 29098748238508265, 30717735339509342, 32380328108694120, 34088662333434598]
  | 5,1 => [0, 0, 15599627679064809, 15599627679064809, 15599627679064809, 15599627679064809, 17856402056721273, 20124745291981436, 22406793172217299, 24704681484800863, 27020546017104126, 29356522556499090, 31714746890357753, 34097354806052116, 36506482090954181, 38944264532435944, 41412837917869407, 43914338034626571, 46450900670079434, 49024661611599997, 51637756646560261]
  | 6,1 => [0, 0, 26966888123638774, 26966888123638774, 26966888123638774, 26966888123638774, 26966888123638774, 30191034469437675, 33428885460212276, 36682576883334578, 39954244526176579, 43246024176110281, 46560051620507682, 49898462646740783, 53263393042181584, 56656978594202086, 60081355090174287]
  | 7,1 => [0, 0, 0, 41676256637920564, 41676256637920564, 41676256637920564, 41676256637920564, 41676256637920564, 45869910739233903, 50079405272894942, 54306876026275681]
  | 6,2 => [0, 0, 87483289404580951, 87483289404580961, 87483289404580975, 87483289404580993, 87483289404581015, 99698781084988573, 111968738617312733, 124301705663343579, 136706225884871188, 149190842943685642, 161764100501577018, 174434542220335400, 187210711761750865, 200101152787613494, 213114408959713367]
  | 7,2 => [0, 0, 0, 157890651360317645, 157890651360317659, 157890651360317677, 157890651360317699, 157890651360317725, 176404816449836122, 194981991053061202, 213630718831783047]
  | _,_ => []

def singleTariff (b j t : ℕ) : ℕ := (singleTariffs j t).getD b 0

private theorem cell_1_3_1 : fatPrice ⟨1,3,1⟩ ≤ singleTariff 1 3 1 := by decide +kernel
private theorem cell_2_3_1 : fatPrice ⟨2,3,1⟩ ≤ singleTariff 2 3 1 := by decide +kernel
private theorem cell_3_3_1 : fatPrice ⟨3,3,1⟩ ≤ singleTariff 3 3 1 := by decide +kernel
private theorem cell_4_3_1 : fatPrice ⟨4,3,1⟩ ≤ singleTariff 4 3 1 := by decide +kernel
private theorem cell_5_3_1 : fatPrice ⟨5,3,1⟩ ≤ singleTariff 5 3 1 := by decide +kernel
private theorem cell_6_3_1 : fatPrice ⟨6,3,1⟩ ≤ singleTariff 6 3 1 := by decide +kernel
private theorem cell_7_3_1 : fatPrice ⟨7,3,1⟩ ≤ singleTariff 7 3 1 := by decide +kernel
private theorem cell_8_3_1 : fatPrice ⟨8,3,1⟩ ≤ singleTariff 8 3 1 := by decide +kernel
private theorem cell_9_3_1 : fatPrice ⟨9,3,1⟩ ≤ singleTariff 9 3 1 := by decide +kernel
private theorem cell_10_3_1 : fatPrice ⟨10,3,1⟩ ≤ singleTariff 10 3 1 := by decide +kernel
private theorem cell_11_3_1 : fatPrice ⟨11,3,1⟩ ≤ singleTariff 11 3 1 := by decide +kernel
private theorem cell_12_3_1 : fatPrice ⟨12,3,1⟩ ≤ singleTariff 12 3 1 := by decide +kernel
private theorem cell_13_3_1 : fatPrice ⟨13,3,1⟩ ≤ singleTariff 13 3 1 := by decide +kernel
private theorem cell_14_3_1 : fatPrice ⟨14,3,1⟩ ≤ singleTariff 14 3 1 := by decide +kernel
private theorem cell_15_3_1 : fatPrice ⟨15,3,1⟩ ≤ singleTariff 15 3 1 := by decide +kernel
private theorem cell_16_3_1 : fatPrice ⟨16,3,1⟩ ≤ singleTariff 16 3 1 := by decide +kernel
private theorem cell_17_3_1 : fatPrice ⟨17,3,1⟩ ≤ singleTariff 17 3 1 := by decide +kernel
private theorem cell_18_3_1 : fatPrice ⟨18,3,1⟩ ≤ singleTariff 18 3 1 := by decide +kernel
private theorem cell_19_3_1 : fatPrice ⟨19,3,1⟩ ≤ singleTariff 19 3 1 := by decide +kernel
private theorem cell_20_3_1 : fatPrice ⟨20,3,1⟩ ≤ singleTariff 20 3 1 := by decide +kernel
private theorem cell_21_3_1 : fatPrice ⟨21,3,1⟩ ≤ singleTariff 21 3 1 := by decide +kernel
private theorem cell_22_3_1 : fatPrice ⟨22,3,1⟩ ≤ singleTariff 22 3 1 := by decide +kernel
private theorem cell_23_3_1 : fatPrice ⟨23,3,1⟩ ≤ singleTariff 23 3 1 := by decide +kernel
private theorem cell_24_3_1 : fatPrice ⟨24,3,1⟩ ≤ singleTariff 24 3 1 := by decide +kernel
private theorem cell_25_3_1 : fatPrice ⟨25,3,1⟩ ≤ singleTariff 25 3 1 := by decide +kernel

private theorem price_3_1 (b : ℕ) (lo : 1≤b) (hi : b≤25) :
    fatPrice ⟨b,3,1⟩ ≤ singleTariff b 3 1 := by
  interval_cases b
  · exact cell_1_3_1
  · exact cell_2_3_1
  · exact cell_3_3_1
  · exact cell_4_3_1
  · exact cell_5_3_1
  · exact cell_6_3_1
  · exact cell_7_3_1
  · exact cell_8_3_1
  · exact cell_9_3_1
  · exact cell_10_3_1
  · exact cell_11_3_1
  · exact cell_12_3_1
  · exact cell_13_3_1
  · exact cell_14_3_1
  · exact cell_15_3_1
  · exact cell_16_3_1
  · exact cell_17_3_1
  · exact cell_18_3_1
  · exact cell_19_3_1
  · exact cell_20_3_1
  · exact cell_21_3_1
  · exact cell_22_3_1
  · exact cell_23_3_1
  · exact cell_24_3_1
  · exact cell_25_3_1

private theorem cell_2_4_1 : fatPrice ⟨2,4,1⟩ ≤ singleTariff 2 4 1 := by decide +kernel
private theorem cell_3_4_1 : fatPrice ⟨3,4,1⟩ ≤ singleTariff 3 4 1 := by decide +kernel
private theorem cell_4_4_1 : fatPrice ⟨4,4,1⟩ ≤ singleTariff 4 4 1 := by decide +kernel
private theorem cell_5_4_1 : fatPrice ⟨5,4,1⟩ ≤ singleTariff 5 4 1 := by decide +kernel
private theorem cell_6_4_1 : fatPrice ⟨6,4,1⟩ ≤ singleTariff 6 4 1 := by decide +kernel
private theorem cell_7_4_1 : fatPrice ⟨7,4,1⟩ ≤ singleTariff 7 4 1 := by decide +kernel
private theorem cell_8_4_1 : fatPrice ⟨8,4,1⟩ ≤ singleTariff 8 4 1 := by decide +kernel
private theorem cell_9_4_1 : fatPrice ⟨9,4,1⟩ ≤ singleTariff 9 4 1 := by decide +kernel
private theorem cell_10_4_1 : fatPrice ⟨10,4,1⟩ ≤ singleTariff 10 4 1 := by decide +kernel
private theorem cell_11_4_1 : fatPrice ⟨11,4,1⟩ ≤ singleTariff 11 4 1 := by decide +kernel
private theorem cell_12_4_1 : fatPrice ⟨12,4,1⟩ ≤ singleTariff 12 4 1 := by decide +kernel
private theorem cell_13_4_1 : fatPrice ⟨13,4,1⟩ ≤ singleTariff 13 4 1 := by decide +kernel
private theorem cell_14_4_1 : fatPrice ⟨14,4,1⟩ ≤ singleTariff 14 4 1 := by decide +kernel
private theorem cell_15_4_1 : fatPrice ⟨15,4,1⟩ ≤ singleTariff 15 4 1 := by decide +kernel
private theorem cell_16_4_1 : fatPrice ⟨16,4,1⟩ ≤ singleTariff 16 4 1 := by decide +kernel
private theorem cell_17_4_1 : fatPrice ⟨17,4,1⟩ ≤ singleTariff 17 4 1 := by decide +kernel
private theorem cell_18_4_1 : fatPrice ⟨18,4,1⟩ ≤ singleTariff 18 4 1 := by decide +kernel
private theorem cell_19_4_1 : fatPrice ⟨19,4,1⟩ ≤ singleTariff 19 4 1 := by decide +kernel
private theorem cell_20_4_1 : fatPrice ⟨20,4,1⟩ ≤ singleTariff 20 4 1 := by decide +kernel
private theorem cell_21_4_1 : fatPrice ⟨21,4,1⟩ ≤ singleTariff 21 4 1 := by decide +kernel
private theorem cell_22_4_1 : fatPrice ⟨22,4,1⟩ ≤ singleTariff 22 4 1 := by decide +kernel
private theorem cell_23_4_1 : fatPrice ⟨23,4,1⟩ ≤ singleTariff 23 4 1 := by decide +kernel

private theorem price_4_1 (b : ℕ) (lo : 2≤b) (hi : b≤23) :
    fatPrice ⟨b,4,1⟩ ≤ singleTariff b 4 1 := by
  interval_cases b
  · exact cell_2_4_1
  · exact cell_3_4_1
  · exact cell_4_4_1
  · exact cell_5_4_1
  · exact cell_6_4_1
  · exact cell_7_4_1
  · exact cell_8_4_1
  · exact cell_9_4_1
  · exact cell_10_4_1
  · exact cell_11_4_1
  · exact cell_12_4_1
  · exact cell_13_4_1
  · exact cell_14_4_1
  · exact cell_15_4_1
  · exact cell_16_4_1
  · exact cell_17_4_1
  · exact cell_18_4_1
  · exact cell_19_4_1
  · exact cell_20_4_1
  · exact cell_21_4_1
  · exact cell_22_4_1
  · exact cell_23_4_1

private theorem cell_2_5_1 : fatPrice ⟨2,5,1⟩ ≤ singleTariff 2 5 1 := by decide +kernel
private theorem cell_3_5_1 : fatPrice ⟨3,5,1⟩ ≤ singleTariff 3 5 1 := by decide +kernel
private theorem cell_4_5_1 : fatPrice ⟨4,5,1⟩ ≤ singleTariff 4 5 1 := by decide +kernel
private theorem cell_5_5_1 : fatPrice ⟨5,5,1⟩ ≤ singleTariff 5 5 1 := by decide +kernel
private theorem cell_6_5_1 : fatPrice ⟨6,5,1⟩ ≤ singleTariff 6 5 1 := by decide +kernel
private theorem cell_7_5_1 : fatPrice ⟨7,5,1⟩ ≤ singleTariff 7 5 1 := by decide +kernel
private theorem cell_8_5_1 : fatPrice ⟨8,5,1⟩ ≤ singleTariff 8 5 1 := by decide +kernel
private theorem cell_9_5_1 : fatPrice ⟨9,5,1⟩ ≤ singleTariff 9 5 1 := by decide +kernel
private theorem cell_10_5_1 : fatPrice ⟨10,5,1⟩ ≤ singleTariff 10 5 1 := by decide +kernel
private theorem cell_11_5_1 : fatPrice ⟨11,5,1⟩ ≤ singleTariff 11 5 1 := by decide +kernel
private theorem cell_12_5_1 : fatPrice ⟨12,5,1⟩ ≤ singleTariff 12 5 1 := by decide +kernel
private theorem cell_13_5_1 : fatPrice ⟨13,5,1⟩ ≤ singleTariff 13 5 1 := by decide +kernel
private theorem cell_14_5_1 : fatPrice ⟨14,5,1⟩ ≤ singleTariff 14 5 1 := by decide +kernel
private theorem cell_15_5_1 : fatPrice ⟨15,5,1⟩ ≤ singleTariff 15 5 1 := by decide +kernel
private theorem cell_16_5_1 : fatPrice ⟨16,5,1⟩ ≤ singleTariff 16 5 1 := by decide +kernel
private theorem cell_17_5_1 : fatPrice ⟨17,5,1⟩ ≤ singleTariff 17 5 1 := by decide +kernel
private theorem cell_18_5_1 : fatPrice ⟨18,5,1⟩ ≤ singleTariff 18 5 1 := by decide +kernel
private theorem cell_19_5_1 : fatPrice ⟨19,5,1⟩ ≤ singleTariff 19 5 1 := by decide +kernel
private theorem cell_20_5_1 : fatPrice ⟨20,5,1⟩ ≤ singleTariff 20 5 1 := by decide +kernel

private theorem price_5_1 (b : ℕ) (lo : 2≤b) (hi : b≤20) :
    fatPrice ⟨b,5,1⟩ ≤ singleTariff b 5 1 := by
  interval_cases b
  · exact cell_2_5_1
  · exact cell_3_5_1
  · exact cell_4_5_1
  · exact cell_5_5_1
  · exact cell_6_5_1
  · exact cell_7_5_1
  · exact cell_8_5_1
  · exact cell_9_5_1
  · exact cell_10_5_1
  · exact cell_11_5_1
  · exact cell_12_5_1
  · exact cell_13_5_1
  · exact cell_14_5_1
  · exact cell_15_5_1
  · exact cell_16_5_1
  · exact cell_17_5_1
  · exact cell_18_5_1
  · exact cell_19_5_1
  · exact cell_20_5_1

private theorem cell_2_6_1 : fatPrice ⟨2,6,1⟩ ≤ singleTariff 2 6 1 := by decide +kernel
private theorem cell_3_6_1 : fatPrice ⟨3,6,1⟩ ≤ singleTariff 3 6 1 := by decide +kernel
private theorem cell_4_6_1 : fatPrice ⟨4,6,1⟩ ≤ singleTariff 4 6 1 := by decide +kernel
private theorem cell_5_6_1 : fatPrice ⟨5,6,1⟩ ≤ singleTariff 5 6 1 := by decide +kernel
private theorem cell_6_6_1 : fatPrice ⟨6,6,1⟩ ≤ singleTariff 6 6 1 := by decide +kernel
private theorem cell_7_6_1 : fatPrice ⟨7,6,1⟩ ≤ singleTariff 7 6 1 := by decide +kernel
private theorem cell_8_6_1 : fatPrice ⟨8,6,1⟩ ≤ singleTariff 8 6 1 := by decide +kernel
private theorem cell_9_6_1 : fatPrice ⟨9,6,1⟩ ≤ singleTariff 9 6 1 := by decide +kernel
private theorem cell_10_6_1 : fatPrice ⟨10,6,1⟩ ≤ singleTariff 10 6 1 := by decide +kernel
private theorem cell_11_6_1 : fatPrice ⟨11,6,1⟩ ≤ singleTariff 11 6 1 := by decide +kernel
private theorem cell_12_6_1 : fatPrice ⟨12,6,1⟩ ≤ singleTariff 12 6 1 := by decide +kernel
private theorem cell_13_6_1 : fatPrice ⟨13,6,1⟩ ≤ singleTariff 13 6 1 := by decide +kernel
private theorem cell_14_6_1 : fatPrice ⟨14,6,1⟩ ≤ singleTariff 14 6 1 := by decide +kernel
private theorem cell_15_6_1 : fatPrice ⟨15,6,1⟩ ≤ singleTariff 15 6 1 := by decide +kernel
private theorem cell_16_6_1 : fatPrice ⟨16,6,1⟩ ≤ singleTariff 16 6 1 := by decide +kernel

private theorem price_6_1 (b : ℕ) (lo : 2≤b) (hi : b≤16) :
    fatPrice ⟨b,6,1⟩ ≤ singleTariff b 6 1 := by
  interval_cases b
  · exact cell_2_6_1
  · exact cell_3_6_1
  · exact cell_4_6_1
  · exact cell_5_6_1
  · exact cell_6_6_1
  · exact cell_7_6_1
  · exact cell_8_6_1
  · exact cell_9_6_1
  · exact cell_10_6_1
  · exact cell_11_6_1
  · exact cell_12_6_1
  · exact cell_13_6_1
  · exact cell_14_6_1
  · exact cell_15_6_1
  · exact cell_16_6_1

private theorem cell_3_7_1 : fatPrice ⟨3,7,1⟩ ≤ singleTariff 3 7 1 := by decide +kernel
private theorem cell_4_7_1 : fatPrice ⟨4,7,1⟩ ≤ singleTariff 4 7 1 := by decide +kernel
private theorem cell_5_7_1 : fatPrice ⟨5,7,1⟩ ≤ singleTariff 5 7 1 := by decide +kernel
private theorem cell_6_7_1 : fatPrice ⟨6,7,1⟩ ≤ singleTariff 6 7 1 := by decide +kernel
private theorem cell_7_7_1 : fatPrice ⟨7,7,1⟩ ≤ singleTariff 7 7 1 := by decide +kernel
private theorem cell_8_7_1 : fatPrice ⟨8,7,1⟩ ≤ singleTariff 8 7 1 := by decide +kernel
private theorem cell_9_7_1 : fatPrice ⟨9,7,1⟩ ≤ singleTariff 9 7 1 := by decide +kernel
private theorem cell_10_7_1 : fatPrice ⟨10,7,1⟩ ≤ singleTariff 10 7 1 := by decide +kernel

private theorem price_7_1 (b : ℕ) (lo : 3≤b) (hi : b≤10) :
    fatPrice ⟨b,7,1⟩ ≤ singleTariff b 7 1 := by
  interval_cases b
  · exact cell_3_7_1
  · exact cell_4_7_1
  · exact cell_5_7_1
  · exact cell_6_7_1
  · exact cell_7_7_1
  · exact cell_8_7_1
  · exact cell_9_7_1
  · exact cell_10_7_1

private theorem cell_2_6_2 : fatPrice ⟨2,6,2⟩ ≤ singleTariff 2 6 2 := by decide +kernel
private theorem cell_3_6_2 : fatPrice ⟨3,6,2⟩ ≤ singleTariff 3 6 2 := by decide +kernel
private theorem cell_4_6_2 : fatPrice ⟨4,6,2⟩ ≤ singleTariff 4 6 2 := by decide +kernel
private theorem cell_5_6_2 : fatPrice ⟨5,6,2⟩ ≤ singleTariff 5 6 2 := by decide +kernel
private theorem cell_6_6_2 : fatPrice ⟨6,6,2⟩ ≤ singleTariff 6 6 2 := by decide +kernel
private theorem cell_7_6_2 : fatPrice ⟨7,6,2⟩ ≤ singleTariff 7 6 2 := by decide +kernel
private theorem cell_8_6_2 : fatPrice ⟨8,6,2⟩ ≤ singleTariff 8 6 2 := by decide +kernel
private theorem cell_9_6_2 : fatPrice ⟨9,6,2⟩ ≤ singleTariff 9 6 2 := by decide +kernel
private theorem cell_10_6_2 : fatPrice ⟨10,6,2⟩ ≤ singleTariff 10 6 2 := by decide +kernel
private theorem cell_11_6_2 : fatPrice ⟨11,6,2⟩ ≤ singleTariff 11 6 2 := by decide +kernel
private theorem cell_12_6_2 : fatPrice ⟨12,6,2⟩ ≤ singleTariff 12 6 2 := by decide +kernel
private theorem cell_13_6_2 : fatPrice ⟨13,6,2⟩ ≤ singleTariff 13 6 2 := by decide +kernel
private theorem cell_14_6_2 : fatPrice ⟨14,6,2⟩ ≤ singleTariff 14 6 2 := by decide +kernel
private theorem cell_15_6_2 : fatPrice ⟨15,6,2⟩ ≤ singleTariff 15 6 2 := by decide +kernel
private theorem cell_16_6_2 : fatPrice ⟨16,6,2⟩ ≤ singleTariff 16 6 2 := by decide +kernel

private theorem price_6_2 (b : ℕ) (lo : 2≤b) (hi : b≤16) :
    fatPrice ⟨b,6,2⟩ ≤ singleTariff b 6 2 := by
  interval_cases b
  · exact cell_2_6_2
  · exact cell_3_6_2
  · exact cell_4_6_2
  · exact cell_5_6_2
  · exact cell_6_6_2
  · exact cell_7_6_2
  · exact cell_8_6_2
  · exact cell_9_6_2
  · exact cell_10_6_2
  · exact cell_11_6_2
  · exact cell_12_6_2
  · exact cell_13_6_2
  · exact cell_14_6_2
  · exact cell_15_6_2
  · exact cell_16_6_2

private theorem cell_3_7_2 : fatPrice ⟨3,7,2⟩ ≤ singleTariff 3 7 2 := by decide +kernel
private theorem cell_4_7_2 : fatPrice ⟨4,7,2⟩ ≤ singleTariff 4 7 2 := by decide +kernel
private theorem cell_5_7_2 : fatPrice ⟨5,7,2⟩ ≤ singleTariff 5 7 2 := by decide +kernel
private theorem cell_6_7_2 : fatPrice ⟨6,7,2⟩ ≤ singleTariff 6 7 2 := by decide +kernel
private theorem cell_7_7_2 : fatPrice ⟨7,7,2⟩ ≤ singleTariff 7 7 2 := by decide +kernel
private theorem cell_8_7_2 : fatPrice ⟨8,7,2⟩ ≤ singleTariff 8 7 2 := by decide +kernel
private theorem cell_9_7_2 : fatPrice ⟨9,7,2⟩ ≤ singleTariff 9 7 2 := by decide +kernel
private theorem cell_10_7_2 : fatPrice ⟨10,7,2⟩ ≤ singleTariff 10 7 2 := by decide +kernel

private theorem price_7_2 (b : ℕ) (lo : 3≤b) (hi : b≤10) :
    fatPrice ⟨b,7,2⟩ ≤ singleTariff b 7 2 := by
  interval_cases b
  · exact cell_3_7_2
  · exact cell_4_7_2
  · exact cell_5_7_2
  · exact cell_6_7_2
  · exact cell_7_7_2
  · exact cell_8_7_2
  · exact cell_9_7_2
  · exact cell_10_7_2

private theorem single_price {b j t : ℕ} (ht : 1≤t) (hj : 3*t≤j)
    (hs : j≤7) (hv : j≤3*b) (hb : b≤degreeCap j) :
    fatPrice ⟨b,j,t⟩≤singleTariff b j t := by
  have ht2 : t≤2 := by omega
  interval_cases t
  · have jl : 3≤j := by omega
    interval_cases j
    · exact price_3_1 b (by omega) hb
    · exact price_4_1 b (by omega) hb
    · exact price_5_1 b (by omega) hb
    · exact price_6_1 b (by omega) hb
    · exact price_7_1 b (by omega) hb
  · have jl : 6≤j := by omega
    interval_cases j
    · exact price_6_2 b (by omega) hb
    · exact price_7_2 b (by omega) hb

private def splitPrices (b j : ℕ) : List ℕ :=
  (List.range (b+1)).flatMap (fun c=>(List.range (j+1)).map (fun k=>
    if 3≤k ∧ k≤3*c ∧ 3≤j-k ∧ j-k≤3*(b-c) then
      singleTariff c k 1+singleTariff (b-c) (j-k) 1 else 0))

private def widthCharge (b j t : ℕ) : ℕ :=
  if t=0 then 0 else
    max (singleTariff b j t) (if t=2 then (splitPrices b j).foldr max 0 else 0)

private theorem le_fold_max {v : ℕ} {L : List ℕ} (mem : v∈L) : v≤L.foldr max 0 := by
  induction L with
  | nil => simp at mem
  | cons a tail ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | m
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih m).trans (le_max_right _ _)

private theorem width_single (b j t : ℕ) (hp : 0<t) : singleTariff b j t≤widthCharge b j t := by
  unfold widthCharge
  rw [ite_eq_right (Nat.ne_of_gt hp)]
  exact le_max_left _ _

private theorem width_pair (b c j k : ℕ) (hj : 3≤j) (hk : 3≤k) (hb : j≤3*b) (hc : k≤3*c) :
    singleTariff b j 1+singleTariff c k 1≤widthCharge (b+c) (j+k) 2 := by
  unfold widthCharge
  rw [ite_eq_right (by decide : ¬(2 : ℕ)=0), ite_eq_left rfl]
  apply le_trans _ (le_max_right _ _)
  apply le_fold_max
  unfold splitPrices
  refine List.mem_flatMap.mpr ⟨b,List.mem_range.mpr (by omega),?_⟩
  refine List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),?_⟩
  rw [show b+c-b=c by omega,show j+k-j=k by omega]
  rw [ite_eq_left ⟨hj,hb,hk,hc⟩]

private theorem checked_row (j : Fin 8) (t : Fin 3) :
    (List.range (degreeCap j.val+1)).all (fun b=>decide
      (1≤t.val → 3*t.val≤j.val → j.val≤3*b → widthCharge b j.val t.val≤retainedTariff b j.val t.val)) = true := by
  fin_cases j <;> fin_cases t <;> decide +kernel

private theorem width_checked {b j t : ℕ} (ht : 1≤t) (hj : 3*t≤j)
    (hs : j≤7) (hv : j≤3*b) (hb : b≤degreeCap j) :
    widthCharge b j t≤retainedTariff b j t := by
  have inj : t<3 := by omega
  have h := List.all_eq_true.mp (checked_row ⟨j,by omega⟩ ⟨t,inj⟩)
    b (List.mem_range.mpr (Nat.lt_succ_of_le hb))
  exact of_decide_eq_true h ht hj hv

/-- Charge a valid retained family at its exact total width. -/
theorem retained_family_fee (n : ℕ) (a : Fin n→Shape) (hv : ∀ i,Valid (a i))
    (hj : (∑ i,(a i).j)≤7) (hb : (∑ i,(a i).b) ≤ degreeCap (∑ i,(a i).j)) :
    (∑ i,fatPrice (a i)) ≤ retainedTariff (∑ i,(a i).b) (∑ i,(a i).j) (∑ i,(a i).t) := by
  have hsum : 3*(∑ i,(a i).t)≤∑ i,(a i).j := by
    rw [Finset.mul_sum]
    exact sum_le_sum fun i _=>(hv i).2.1
  have hn' : n≤∑ i,(a i).t := calc
    n = ∑ _ : Fin n,1 := by simp
    _ ≤ ∑ i,(a i).t := sum_le_sum fun i _=>(hv i).1
  have hn : n≤2 := by omega
  interval_cases n
  · simp
  · simp only [Fin.sum_univ_one] at hj hb ⊢
    have one := hv 0
    have eq : a 0=⟨(a 0).b,(a 0).j,(a 0).t⟩ := by cases a 0; rfl
    conv_lhs => rw [eq]
    exact (single_price one.1 one.2.1 hj one.2.2 hb).trans
      ((width_single _ _ _ one.1).trans (width_checked one.1 one.2.1 hj one.2.2 hb))
  · simp only [Fin.sum_univ_two] at hsum hj hb ⊢
    have ht0 : (a 0).t=1 := by have := (hv 0).1; have := (hv 1).1; omega
    have ht1 : (a 1).t=1 := by have := (hv 0).1; have := (hv 1).1; omega
    have he (i : Fin 2) : a i=⟨(a i).b,(a i).j,(a i).t⟩ := by cases a i; rfl
    have shape0 : a 0=⟨(a 0).b,(a 0).j,1⟩ :=
      (he 0).trans (congrArg (fun t=>(⟨(a 0).b,(a 0).j,t⟩ : Shape)) ht0)
    have shape1 : a 1=⟨(a 1).b,(a 1).j,1⟩ :=
      (he 1).trans (congrArg (fun t=>(⟨(a 1).b,(a 1).j,t⟩ : Shape)) ht1)
    have hj0 : 3≤(a 0).j := by simpa only [ht0,Nat.mul_one] using (hv 0).2.1
    have hj1 : 3≤(a 1).j := by simpa only [ht1,Nat.mul_one] using (hv 1).2.1
    have j0hi : (a 0).j≤4 := by omega
    have j1hi : (a 1).j≤4 := by omega
    have totalB : (a 0).b+(a 1).b≤16 := by
      apply hb.trans
      have eq : (a 0).j+(a 1).j=6 ∨ (a 0).j+(a 1).j=7 := by omega
      rcases eq with eq | eq <;> rw [eq] <;> decide
    have below (j : ℕ) (lo : 3≤j) (hi : j≤4) : 16≤degreeCap j := by
      interval_cases j <;> decide
    have p0 := single_price (b:=(a 0).b) (t:=1) (by decide) (by simpa using hj0) (by omega)
      (hv 0).2.2 ((by omega : (a 0).b≤16).trans (below _ hj0 j0hi))
    have p1 := single_price (b:=(a 1).b) (t:=1) (by decide) (by simpa using hj1) (by omega)
      (hv 1).2.2 ((by omega : (a 1).b≤16).trans (below _ hj1 j1hi))
    rw [←shape0] at p0
    rw [←shape1] at p1
    have h := width_pair (a 0).b (a 1).b (a 0).j (a 1).j hj0 hj1 (hv 0).2.2 (hv 1).2.2
    rw [ht0,ht1]
    exact (Nat.add_le_add p0 p1).trans (h.trans (width_checked (by decide) (by omega) hj (by
      have := (hv 0).2.2; have := (hv 1).2.2; omega) hb))

#print axioms retained_family_fee
end Lower6960.Low
