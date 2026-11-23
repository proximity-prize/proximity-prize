import ProximityPrize.SubmissionLower.KoalaWeightedReceipt2428
import ProximityPrize.SubmissionLower.Final50PriceCaps
import ProximityPrize.SubmissionLower.Final50PriceReceipt

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option linter.defProp false

namespace Final50PriceActualOrder
open Final50PriceCaps (Band start)
open Final50Price (layerNeed)
open K1_13 (Shape InBox)
open Final50PriceLayer (availableMass)
open Final50PriceReceipt (Prefix makePrefix checks)

private theorem paid (r : Shape) (table : Prefix r.b r.j) (b j l : Nat) (values : List Nat)
    (hr : r.j = 0 → r.b = 0 := by decide)
    (h : checks r table b j l values = true := by decide +kernel) :
    availableMass r ⟨b,j,0⟩ l < layerNeed :=
  (Final50PriceReceipt.paid r table b j l values hr h).2

private def prefix_3_4 := makePrefix 3 4 [
  (60, 19418843666604)]
private def prefix_3_6 := makePrefix 3 6 [
  (75, 20092810174690)]
private def prefix_4_4 := makePrefix 4 4 [
  (61, 19492245430426)]
private def prefix_4_7 := makePrefix 4 7 [
  (92, 20457672280554)]
private def prefix_5_4 := makePrefix 5 4 [
  (62, 19553890309795)]
private def prefix_5_6 := makePrefix 5 6 [
  (77, 19986593483626), (78, 20129191438642), (79, 20269532639396)]
private def prefix_5_7 := makePrefix 5 7 [
  (95, 20484453470212), (96, 20565469706208)]
private def prefix_6_4 := makePrefix 6 4 [
  (63, 19603684502290)]
private def prefix_6_6 := makePrefix 6 6 [
  (79, 20055936872560), (80, 20190455071788), (81, 20322776795868)]
private def prefix_6_7 := makePrefix 6 7 [
  (99, 20553237935289)]
private def prefix_7_4 := makePrefix 7 4 [
  (64, 19641538453472)]
private def prefix_7_6 := makePrefix 7 6 [
  (81, 20102009293602), (82, 20228590766682), (83, 20353038557826)]
private def prefix_8_4 := makePrefix 8 4 [
  (65, 19667366807486)]
private def prefix_8_6 := makePrefix 8 6 [
  (84, 20243940722999), (85, 20360667981297)]
private def prefix_9_4 := makePrefix 9 4 [
  (67, 19886209615855)]
private def prefix_9_6 := makePrefix 9 6 [
  (86, 20236868650190), (87, 20346036071924)]
private def prefix_10_4 := makePrefix 10 4 [
  (68, 19880470549020)]
private def prefix_10_6 := makePrefix 10 6 [
  (89, 20309533399254), (90, 20409402740652)]
private def prefix_11_4 := makePrefix 11 4 [
  (69, 19862434850850)]
private def prefix_11_6 := makePrefix 11 6 [
  (93, 20435203531892), (94, 20524334815224)]
private def prefix_11_7 := makePrefix 11 7 [
  (138, 20777021816582), (139, 20796048315656)]
private def prefix_12_4 := makePrefix 12 4 [
  (71, 20012890559132)]
private def prefix_12_7 := makePrefix 12 7 [
  (185, 20842235387064), (186, 20844191300312)]
private def prefix_13_4 := makePrefix 13 4 [
  (72, 19962675696632)]
private def prefix_13_6 := makePrefix 13 6 [
  (102, 20591788893642)]
private def prefix_14_4 := makePrefix 14 4 [
  (74, 20063686041282)]
private def prefix_15_4 := makePrefix 15 4 [
  (76, 20134957702160)]
private def prefix_16_4 := makePrefix 16 4 [
  (78, 20176409060730)]
private def prefix_16_6 := makePrefix 16 6 [
  (124, 20710272663537), (125, 20743060099575)]
private def prefix_17_4 := makePrefix 17 4 [
  (80, 20187985783773)]
private def prefix_18_4 := makePrefix 18 4 [
  (83, 20292410859016)]
private def prefix_19_4 := makePrefix 19 4 [
  (86, 20345626418333)]
private def prefix_20_4 := makePrefix 20 4 [
  (90, 20445431988982)]
private def prefix_21_4 := makePrefix 21 4 [
  (95, 20552563208564)]
private def prefix_22_4 := makePrefix 22 4 [
  (101, 20624706627918)]
private def prefix_23_4 := makePrefix 23 4 [
  (110, 20712266608009)]
private def prefix_24_4 := makePrefix 24 4 [
  (131, 20823972165175)]

private def r_two6thinwide_11_95_0 := paid ⟨11,6,2⟩ prefix_11_6 124 50 94 [316093532138]
private def r_two6thinwide_11_95_1 := paid ⟨11,6,2⟩ prefix_11_6 126 49 94 [319502401774]
private def r_two6thinwide_11_94_0 := paid ⟨11,6,2⟩ prefix_11_6 124 38 93 [391708948421]
private def r_two6wider_16_126_0 := paid ⟨16,6,2⟩ prefix_16_6 104 50 125 [91369018944]
private def r_two6wider_16_126_1 := paid ⟨16,6,2⟩ prefix_16_6 106 49 125 [92166119894]
private def r_two6wider_16_126_2 := paid ⟨16,6,2⟩ prefix_16_6 108 48 125 [92949728046]
private def r_two6wider_16_126_3 := paid ⟨16,6,2⟩ prefix_16_6 110 47 125 [93716707163]
private def r_two6wider_16_126_4 := paid ⟨16,6,2⟩ prefix_16_6 111 46 125 [94771067568]
private def r_two6wider_16_126_5 := paid ⟨16,6,2⟩ prefix_16_6 113 45 125 [95506687289]
private def r_two6wider_16_126_6 := paid ⟨16,6,2⟩ prefix_16_6 115 44 125 [96217094448]
private def r_two6wider_16_126_7 := paid ⟨16,6,2⟩ prefix_16_6 117 38 125 [103921825758]
private def r_two6wider_16_126_8 := paid ⟨16,6,2⟩ prefix_16_6 120 37 125 [104098737509]
private def r_two6wider_16_125_0 := paid ⟨16,6,2⟩ prefix_16_6 111 38 124 [110369026417]
private def r_two6wider_16_125_1 := paid ⟨16,6,2⟩ prefix_16_6 115 37 124 [110188160278]
private def r_two6wider_16_125_2 := paid ⟨16,6,2⟩ prefix_16_6 119 36 124 [109910861470]
private def r_two6wider_16_125_3 := paid ⟨16,6,2⟩ prefix_16_6 121 35 124 [110485809020]
private def r_two7last_11_140_0 := paid ⟨11,7,2⟩ prefix_11_7 101 49 139 [43162444692]
private def r_two7last_11_140_1 := paid ⟨11,7,2⟩ prefix_11_7 103 48 139 [43838688356]
private def r_two7last_11_140_2 := paid ⟨11,7,2⟩ prefix_11_7 104 47 139 [44598880536]
private def r_two7last_11_140_3 := paid ⟨11,7,2⟩ prefix_11_7 105 46 139 [45379824494]
private def r_two7last_11_140_4 := paid ⟨11,7,2⟩ prefix_11_7 107 45 139 [46107918193]
private def r_two7last_11_140_5 := paid ⟨11,7,2⟩ prefix_11_7 109 44 139 [46852163650]
private def r_two7last_11_140_6 := paid ⟨11,7,2⟩ prefix_11_7 111 43 139 [47612851737]
private def r_two7last_11_140_7 := paid ⟨11,7,2⟩ prefix_11_7 113 42 139 [48390139078]
private def r_two7last_11_140_8 := paid ⟨11,7,2⟩ prefix_11_7 116 41 139 [49096807396]
private def r_two7last_11_140_9 := paid ⟨11,7,2⟩ prefix_11_7 118 40 139 [49903607004]
private def r_two7last_11_140_10 := paid ⟨11,7,2⟩ prefix_11_7 121 39 139 [50631752402]
private def r_two7last_11_140_11 := paid ⟨11,7,2⟩ prefix_11_7 126 38 139 [51168737778]
private def r_two7last_11_139_0 := paid ⟨11,7,2⟩ prefix_11_7 111 38 138 [55078857912]
private def r_two7last_11_139_1 := paid ⟨11,7,2⟩ prefix_11_7 115 37 138 [55802087940]
private def r_two7last_11_139_2 := paid ⟨11,7,2⟩ prefix_11_7 119 36 138 [56523962256]
private def r_two7last_11_139_3 := paid ⟨11,7,2⟩ prefix_11_7 122 35 138 [57361941984]
private def r_two7last_11_139_4 := paid ⟨11,7,2⟩ prefix_11_7 126 34 138 [58078483594]
private def r_two7last_12_187_0 := paid ⟨12,7,2⟩ prefix_12_7 15 44 186 [2452968674]
private def r_two7last_12_187_1 := paid ⟨12,7,2⟩ prefix_12_7 59 43 186 [2390489462]
private def r_two7last_12_187_2 := paid ⟨12,7,2⟩ prefix_12_7 60 42 186 [2448940141]
private def r_two7last_12_187_3 := paid ⟨12,7,2⟩ prefix_12_7 61 41 186 [2509557736]
private def r_two7last_12_187_4 := paid ⟨12,7,2⟩ prefix_12_7 62 40 186 [2572472674]
private def r_two7last_12_187_5 := paid ⟨12,7,2⟩ prefix_12_7 63 39 186 [2637823727]
private def r_two7last_12_187_6 := paid ⟨12,7,2⟩ prefix_12_7 64 38 186 [2705736552]
private def r_two7last_12_187_7 := paid ⟨12,7,2⟩ prefix_12_7 66 36 186 [2849747075]
private def r_two7last_12_187_8 := paid ⟨12,7,2⟩ prefix_12_7 68 35 186 [2922048994]
private def r_two7last_12_187_9 := paid ⟨12,7,2⟩ prefix_12_7 69 34 186 [3001475680]
private def r_two7last_12_187_10 := paid ⟨12,7,2⟩ prefix_12_7 71 33 186 [3079740353]
private def r_two7last_12_187_11 := paid ⟨12,7,2⟩ prefix_12_7 88 32 186 [3089111710]
private def r_two7last_12_187_12 := paid ⟨12,7,2⟩ prefix_12_7 106 31 186 [3088825342]
private def r_two7last_12_187_13 := paid ⟨12,7,2⟩ prefix_12_7 123 30 186 [3087958034]
private def r_two7last_12_186_0 := paid ⟨12,7,2⟩ prefix_12_7 73 32 185 [3452229393]
private def r_two7last_12_186_1 := paid ⟨12,7,2⟩ prefix_12_7 75 31 185 [3543840583]
private def r_two7last_12_186_2 := paid ⟨12,7,2⟩ prefix_12_7 77 30 185 [3639168834]
private def r_two7last_12_186_3 := paid ⟨12,7,2⟩ prefix_12_7 80 29 185 [3732155199]
private def r_two7last_12_186_4 := paid ⟨12,7,2⟩ prefix_12_7 82 28 185 [3835086092]
private def r_two7last_12_186_5 := paid ⟨12,7,2⟩ prefix_12_7 85 27 185 [3935283910]
private def r_two7last_12_186_6 := paid ⟨12,7,2⟩ prefix_12_7 87 26 185 [4046557102]
private def r_two7last_12_186_7 := paid ⟨12,7,2⟩ prefix_12_7 90 25 185 [4154559302]
private def r_two7last_12_186_8 := paid ⟨12,7,2⟩ prefix_12_7 94 24 185 [4257938001]
private def r_two7last_12_186_9 := paid ⟨12,7,2⟩ prefix_12_7 98 23 185 [4364046225]
private def r_two7last_12_186_10 := paid ⟨12,7,2⟩ prefix_12_7 103 22 185 [4463022079]
private def r_two7last_12_186_11 := paid ⟨12,7,2⟩ prefix_12_7 108 21 185 [4562864106]
private def r_two7last_12_186_12 := paid ⟨12,7,2⟩ prefix_12_7 113 20 185 [4662942585]
private def r_two7last_12_186_13 := paid ⟨12,7,2⟩ prefix_12_7 120 19 185 [4738298937]

private theorem chart_two6thinwide_11_95 (b j t : ℕ) (h : (124 ≤ b ∧ 50 ≤ j) ∨ (126 ≤ b ∧ 49 ≤ j)) :
    availableMass ⟨11,6,2⟩ ⟨b,j,t⟩ 94 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,6,2⟩)
      (y:=⟨124,50,0⟩) (x:=⟨b,j,t⟩) (L:=94) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6thinwide_11_95_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,6,2⟩)
      (y:=⟨126,49,0⟩) (x:=⟨b,j,t⟩) (L:=94) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6thinwide_11_95_1

private theorem chart_two6thinwide_11_94 (b j t : ℕ) (h : (124 ≤ b ∧ 38 ≤ j)) :
    availableMass ⟨11,6,2⟩ ⟨b,j,t⟩ 93 < layerNeed:=by
  rcases h with ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,6,2⟩)
      (y:=⟨124,38,0⟩) (x:=⟨b,j,t⟩) (L:=93) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6thinwide_11_94_0

private theorem chart_two6wider_16_126 (b j t : ℕ) (h : (104 ≤ b ∧ 50 ≤ j) ∨ (106 ≤ b ∧ 49 ≤ j) ∨ (108 ≤ b ∧ 48 ≤ j) ∨ (110 ≤ b ∧ 47 ≤ j) ∨ (111 ≤ b ∧ 46 ≤ j) ∨ (113 ≤ b ∧ 45 ≤ j) ∨ (115 ≤ b ∧ 44 ≤ j) ∨ (117 ≤ b ∧ 38 ≤ j) ∨ (120 ≤ b ∧ 37 ≤ j)) :
    availableMass ⟨16,6,2⟩ ⟨b,j,t⟩ 125 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨104,50,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨106,49,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_1
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨108,48,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_2
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨110,47,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_3
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨111,46,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_4
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨113,45,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_5
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨115,44,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_6
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨117,38,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_7
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨120,37,0⟩) (x:=⟨b,j,t⟩) (L:=125) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_126_8

private theorem chart_two6wider_16_125 (b j t : ℕ) (h : (111 ≤ b ∧ 38 ≤ j) ∨ (115 ≤ b ∧ 37 ≤ j) ∨ (119 ≤ b ∧ 36 ≤ j) ∨ (121 ≤ b ∧ 35 ≤ j)) :
    availableMass ⟨16,6,2⟩ ⟨b,j,t⟩ 124 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨111,38,0⟩) (x:=⟨b,j,t⟩) (L:=124) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_125_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨115,37,0⟩) (x:=⟨b,j,t⟩) (L:=124) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_125_1
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨119,36,0⟩) (x:=⟨b,j,t⟩) (L:=124) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_125_2
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨16,6,2⟩)
      (y:=⟨121,35,0⟩) (x:=⟨b,j,t⟩) (L:=124) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two6wider_16_125_3

private theorem chart_two7last_11_140 (b j t : ℕ) (h : (101 ≤ b ∧ 49 ≤ j) ∨ (103 ≤ b ∧ 48 ≤ j) ∨ (104 ≤ b ∧ 47 ≤ j) ∨ (105 ≤ b ∧ 46 ≤ j) ∨ (107 ≤ b ∧ 45 ≤ j) ∨ (109 ≤ b ∧ 44 ≤ j) ∨ (111 ≤ b ∧ 43 ≤ j) ∨ (113 ≤ b ∧ 42 ≤ j) ∨ (116 ≤ b ∧ 41 ≤ j) ∨ (118 ≤ b ∧ 40 ≤ j) ∨ (121 ≤ b ∧ 39 ≤ j) ∨ (126 ≤ b ∧ 38 ≤ j)) :
    availableMass ⟨11,7,2⟩ ⟨b,j,t⟩ 139 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨101,49,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨103,48,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_1
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨104,47,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_2
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨105,46,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_3
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨107,45,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_4
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨109,44,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_5
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨111,43,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_6
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨113,42,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_7
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨116,41,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_8
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨118,40,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_9
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨121,39,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_10
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨126,38,0⟩) (x:=⟨b,j,t⟩) (L:=139) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_140_11

private theorem chart_two7last_11_139 (b j t : ℕ) (h : (111 ≤ b ∧ 38 ≤ j) ∨ (115 ≤ b ∧ 37 ≤ j) ∨ (119 ≤ b ∧ 36 ≤ j) ∨ (122 ≤ b ∧ 35 ≤ j) ∨ (126 ≤ b ∧ 34 ≤ j)) :
    availableMass ⟨11,7,2⟩ ⟨b,j,t⟩ 138 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨111,38,0⟩) (x:=⟨b,j,t⟩) (L:=138) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_139_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨115,37,0⟩) (x:=⟨b,j,t⟩) (L:=138) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_139_1
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨119,36,0⟩) (x:=⟨b,j,t⟩) (L:=138) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_139_2
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨122,35,0⟩) (x:=⟨b,j,t⟩) (L:=138) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_139_3
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨11,7,2⟩)
      (y:=⟨126,34,0⟩) (x:=⟨b,j,t⟩) (L:=138) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_11_139_4

private theorem chart_two7last_12_187 (b j t : ℕ) (h : (15 ≤ b ∧ 44 ≤ j) ∨ (59 ≤ b ∧ 43 ≤ j) ∨ (60 ≤ b ∧ 42 ≤ j) ∨ (61 ≤ b ∧ 41 ≤ j) ∨ (62 ≤ b ∧ 40 ≤ j) ∨ (63 ≤ b ∧ 39 ≤ j) ∨ (64 ≤ b ∧ 38 ≤ j) ∨ (66 ≤ b ∧ 36 ≤ j) ∨ (68 ≤ b ∧ 35 ≤ j) ∨ (69 ≤ b ∧ 34 ≤ j) ∨ (71 ≤ b ∧ 33 ≤ j) ∨ (88 ≤ b ∧ 32 ≤ j) ∨ (106 ≤ b ∧ 31 ≤ j) ∨ (123 ≤ b ∧ 30 ≤ j)) :
    availableMass ⟨12,7,2⟩ ⟨b,j,t⟩ 186 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨15,44,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨59,43,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_1
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨60,42,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_2
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨61,41,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_3
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨62,40,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_4
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨63,39,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_5
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨64,38,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_6
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨66,36,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_7
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨68,35,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_8
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨69,34,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_9
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨71,33,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_10
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨88,32,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_11
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨106,31,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_12
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨123,30,0⟩) (x:=⟨b,j,t⟩) (L:=186) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_187_13

private theorem chart_two7last_12_186 (b j t : ℕ) (h : (73 ≤ b ∧ 32 ≤ j) ∨ (75 ≤ b ∧ 31 ≤ j) ∨ (77 ≤ b ∧ 30 ≤ j) ∨ (80 ≤ b ∧ 29 ≤ j) ∨ (82 ≤ b ∧ 28 ≤ j) ∨ (85 ≤ b ∧ 27 ≤ j) ∨ (87 ≤ b ∧ 26 ≤ j) ∨ (90 ≤ b ∧ 25 ≤ j) ∨ (94 ≤ b ∧ 24 ≤ j) ∨ (98 ≤ b ∧ 23 ≤ j) ∨ (103 ≤ b ∧ 22 ≤ j) ∨ (108 ≤ b ∧ 21 ≤ j) ∨ (113 ≤ b ∧ 20 ≤ j) ∨ (120 ≤ b ∧ 19 ≤ j)) :
    availableMass ⟨12,7,2⟩ ⟨b,j,t⟩ 185 < layerNeed:=by
  rcases h with ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩ | ⟨hb,hj⟩
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨73,32,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_0
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨75,31,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_1
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨77,30,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_2
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨80,29,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_3
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨82,28,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_4
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨85,27,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_5
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨87,26,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_6
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨90,25,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_7
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨94,24,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_8
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨98,23,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_9
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨103,22,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_10
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨108,21,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_11
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨113,20,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_12
  · exact (Final50PriceLayer.availableMass_anti_prefix (r := ⟨12,7,2⟩)
      (y:=⟨120,19,0⟩) (x:=⟨b,j,t⟩) (L:=185) (Or.inr (by decide)) (by decide) hb hj).trans_lt r_two7last_12_186_13

def raisedPlain (k : Band) (b j q l : ℕ) : ℕ :=
  if k = .two6thinwide ∧ q=11 ∧ ((124≤b ∧ 50≤j) ∨ (126≤b ∧ 49≤j)) then max l 95
  else if k = .two6thinwide ∧ q=11 ∧ ((124≤b ∧ 38≤j)) then max l 94
  else if k = .two6wider ∧ q=16 ∧ ((104≤b ∧ 50≤j) ∨ (106≤b ∧ 49≤j) ∨ (108≤b ∧ 48≤j) ∨ (110≤b ∧ 47≤j) ∨ (111≤b ∧ 46≤j) ∨ (113≤b ∧ 45≤j) ∨ (115≤b ∧ 44≤j) ∨ (117≤b ∧ 38≤j) ∨ (120≤b ∧ 37≤j)) then max l 126
  else if k = .two6wider ∧ q=16 ∧ ((111≤b ∧ 38≤j) ∨ (115≤b ∧ 37≤j) ∨ (119≤b ∧ 36≤j) ∨ (121≤b ∧ 35≤j)) then max l 125
  else if k = .two7last ∧ q=11 ∧ ((101≤b ∧ 49≤j) ∨ (103≤b ∧ 48≤j) ∨ (104≤b ∧ 47≤j) ∨ (105≤b ∧ 46≤j) ∨ (107≤b ∧ 45≤j) ∨ (109≤b ∧ 44≤j) ∨ (111≤b ∧ 43≤j) ∨ (113≤b ∧ 42≤j) ∨ (116≤b ∧ 41≤j) ∨ (118≤b ∧ 40≤j) ∨ (121≤b ∧ 39≤j) ∨ (126≤b ∧ 38≤j)) then max l 140
  else if k = .two7last ∧ q=11 ∧ ((111≤b ∧ 38≤j) ∨ (115≤b ∧ 37≤j) ∨ (119≤b ∧ 36≤j) ∨ (122≤b ∧ 35≤j) ∨ (126≤b ∧ 34≤j)) then max l 139
  else if k = .two7last ∧ q=12 ∧ ((15≤b ∧ 44≤j) ∨ (59≤b ∧ 43≤j) ∨ (60≤b ∧ 42≤j) ∨ (61≤b ∧ 41≤j) ∨ (62≤b ∧ 40≤j) ∨ (63≤b ∧ 39≤j) ∨ (64≤b ∧ 38≤j) ∨ (66≤b ∧ 36≤j) ∨ (68≤b ∧ 35≤j) ∨ (69≤b ∧ 34≤j) ∨ (71≤b ∧ 33≤j) ∨ (88≤b ∧ 32≤j) ∨ (106≤b ∧ 31≤j) ∨ (123≤b ∧ 30≤j)) then max l 187
  else if k = .two7last ∧ q=12 ∧ ((73≤b ∧ 32≤j) ∨ (75≤b ∧ 31≤j) ∨ (77≤b ∧ 30≤j) ∨ (80≤b ∧ 29≤j) ∨ (82≤b ∧ 28≤j) ∨ (85≤b ∧ 27≤j) ∨ (87≤b ∧ 26≤j) ∨ (90≤b ∧ 25≤j) ∨ (94≤b ∧ 24≤j) ∨ (98≤b ∧ 23≤j) ∨ (103≤b ∧ 22≤j) ∨ (108≤b ∧ 21≤j) ∨ (113≤b ∧ 20≤j) ∨ (120≤b ∧ 19≤j)) then max l 186
  else l

theorem raisedPlain_pos {k : Band} {b j q l : ℕ} (h : 0 < l) : 0 < raisedPlain k b j q l := by
  unfold raisedPlain
  repeat' split
  all_goals omega

theorem raisedPlain_valid (k : Band) (b j t q l : ℕ) :
    raisedPlain k b j q l ≤ l ∨
      availableMass ⟨q,(start k).j,(start k).t⟩ ⟨b,j,t⟩ (raisedPlain k b j q l-1) < layerNeed:=by
  unfold raisedPlain
  split
  · rename_i h
    rcases h with ⟨rfl,rfl,h⟩
    by_cases hl:95≤l
    · exact Or.inl (max_le le_rfl hl)
    rw [max_eq_right (by omega:l≤95)]
    exact Or.inr (chart_two6thinwide_11_95 b j t h)
  · split
    · rename_i h
      rcases h with ⟨rfl,rfl,h⟩
      by_cases hl:94≤l
      · exact Or.inl (max_le le_rfl hl)
      rw [max_eq_right (by omega:l≤94)]
      exact Or.inr (chart_two6thinwide_11_94 b j t h)
    · split
      · rename_i h
        rcases h with ⟨rfl,rfl,h⟩
        by_cases hl:126≤l
        · exact Or.inl (max_le le_rfl hl)
        rw [max_eq_right (by omega:l≤126)]
        exact Or.inr (chart_two6wider_16_126 b j t h)
      · split
        · rename_i h
          rcases h with ⟨rfl,rfl,h⟩
          by_cases hl:125≤l
          · exact Or.inl (max_le le_rfl hl)
          rw [max_eq_right (by omega:l≤125)]
          exact Or.inr (chart_two6wider_16_125 b j t h)
        · split
          · rename_i h
            rcases h with ⟨rfl,rfl,h⟩
            by_cases hl:140≤l
            · exact Or.inl (max_le le_rfl hl)
            rw [max_eq_right (by omega:l≤140)]
            exact Or.inr (chart_two7last_11_140 b j t h)
          · split
            · rename_i h
              rcases h with ⟨rfl,rfl,h⟩
              by_cases hl:139≤l
              · exact Or.inl (max_le le_rfl hl)
              rw [max_eq_right (by omega:l≤139)]
              exact Or.inr (chart_two7last_11_139 b j t h)
            · split
              · rename_i h
                rcases h with ⟨rfl,rfl,h⟩
                by_cases hl:187≤l
                · exact Or.inl (max_le le_rfl hl)
                rw [max_eq_right (by omega:l≤187)]
                exact Or.inr (chart_two7last_12_187 b j t h)
              · split
                · rename_i h
                  rcases h with ⟨rfl,rfl,h⟩
                  by_cases hl:186≤l
                  · exact Or.inl (max_le le_rfl hl)
                  rw [max_eq_right (by omega:l≤186)]
                  exact Or.inr (chart_two7last_12_186 b j t h)
                · exact Or.inl le_rfl


open KoalaWeightedReceipt2428 (WeightedOrder)
open private KoalaWeightedReceipt2428.retained from ProximityPrize.SubmissionLower.KoalaWeightedReceipt2428

private theorem weightedRetained :
    InBox KoalaWeightedReceipt2428.retained ⟨11, (start Band.two7last).j, (start Band.two7last).t⟩ := by
  unfold InBox
  decide

private def at141:List (ℕ × ℕ × ℕ):=[(123,49,2),(124,49,2),(124,49,3),(124,49,4),(125,48,2),(125,49,4),(126,48,2),(126,48,3),(126,49,5)]
private def at142:List (ℕ × ℕ × ℕ):=[(125,49,2),(125,49,3),(126,49,2),(126,49,3),(126,49,4)]

private def weightedTarget (k : Band) (b j t q : ℕ) : ℕ :=
  if k = .two7last ∧ q=11 ∧ 125≤b ∧ 49≤j ∧ (b,j,t) ∈ at142 then 142
  else if k = .two7last ∧ q=11 ∧ 123≤b ∧ 48≤j ∧ (b,j,t) ∈ at141 then 141
  else 0

def raisedBefore (k : Band) (b j t q l : ℕ) : ℕ :=
  max (raisedPlain k b j q l) (weightedTarget k b j t q)

theorem raisedBefore_pos {k : Band} {b j t q l : ℕ} (h : 0 < l) : 0 < raisedBefore k b j t q l :=
  (raisedPlain_pos h).trans_le (le_max_left _ _)

theorem raisedBefore_valid (k : Band) (b j t q l : ℕ) :
    raisedBefore k b j t q l ≤ l ∨
      availableMass ⟨q,(start k).j,(start k).t⟩ ⟨b,j,t⟩ (raisedBefore k b j t q l-1) < layerNeed ∨
        WeightedOrder ⟨q,(start k).j,(start k).t⟩ ⟨b,j,t⟩ (raisedBefore k b j t q l):=by
  unfold raisedBefore
  by_cases h:weightedTarget k b j t q≤raisedPlain k b j q l
  · rw [max_eq_left h]
    exact (raisedPlain_valid k b j t q l).imp id Or.inl
  rw [max_eq_right (le_of_lt (Nat.lt_of_not_ge h))]
  right
  right
  by_cases ha:k = .two7last ∧ q=11 ∧ 125≤b ∧ 49≤j ∧ (b,j,t) ∈ at142
  · rw [weightedTarget, if_pos ha]
    rcases ha with ⟨rfl,rfl,hb,hj,_⟩
    exact ⟨weightedRetained, Or.inr ⟨le_rfl,hb,hj⟩⟩
  · by_cases hb : k = .two7last ∧ q = 11 ∧ 123 ≤ b ∧ 48 ≤ j ∧ (b,j,t) ∈ at141
    · rw [weightedTarget, if_neg ha, if_pos hb]
      rcases hb with ⟨rfl,rfl,hb,hj,_⟩
      exact ⟨weightedRetained, Or.inl ⟨le_rfl,hb,hj⟩⟩
    · simp [weightedTarget,ha,hb] at h

private def p2429_0 := paid ⟨3,4,1⟩ prefix_3_4 111 52 60 [1234797513556]
private def p2429_1 := paid ⟨4,4,1⟩ prefix_4_4 111 52 61 [1190646914633]
private def p2429_2 := paid ⟨5,4,1⟩ prefix_5_4 111 52 62 [1146430592568]
private def p2429_3 := paid ⟨6,4,1⟩ prefix_6_4 111 52 63 [1102169371080]
private def p2429_4 := paid ⟨7,4,1⟩ prefix_7_4 111 52 64 [1057883613640]
private def p2429_5 := paid ⟨8,4,1⟩ prefix_8_4 111 52 65 [1013593233408]
private def p2429_6 := paid ⟨9,4,1⟩ prefix_9_4 111 52 67 [955522087144]
private def p2429_7 := paid ⟨10,4,1⟩ prefix_10_4 111 52 68 [911385325252]
private def p2429_8 := paid ⟨11,4,1⟩ prefix_11_4 111 52 69 [867312644632]
private def p2429_9 := paid ⟨12,4,1⟩ prefix_12_4 111 52 71 [810047806824]
private def p2429_10 := paid ⟨13,4,1⟩ prefix_13_4 111 52 72 [766299718512]
private def p2429_11 := paid ⟨14,4,1⟩ prefix_14_4 111 52 74 [709880815722]
private def p2429_12 := paid ⟨15,4,1⟩ prefix_15_4 111 52 76 [654122736168]
private def p2429_13 := paid ⟨16,4,1⟩ prefix_16_4 111 52 78 [599082586484]
private def p2429_14 := paid ⟨17,4,1⟩ prefix_17_4 111 52 80 [544823058744]
private def p2429_15 := paid ⟨18,4,1⟩ prefix_18_4 111 52 83 [480297728626]
private def p2429_16 := paid ⟨19,4,1⟩ prefix_19_4 111 52 86 [417739008229]
private def p2429_17 := paid ⟨20,4,1⟩ prefix_20_4 111 52 90 [347620340937]
private def p2429_18 := paid ⟨21,4,1⟩ prefix_21_4 111 52 95 [272687698600]
private def p2429_19 := paid ⟨22,4,1⟩ prefix_22_4 111 52 101 [196551799286]
private def p2429_20 := paid ⟨23,4,1⟩ prefix_23_4 111 52 110 [112307516741]
private def p2429_21 := paid ⟨24,4,1⟩ prefix_24_4 111 52 131 [15626026466]
private def p2429_22 := paid ⟨3,6,2⟩ prefix_3_6 129 47 75 [679343664104]
private def p2429_23 := paid ⟨3,6,2⟩ prefix_3_6 129 49 75 [657703931803]
private def p2429_24 := paid ⟨3,6,2⟩ prefix_3_6 130 46 75 [689320582264]
private def p2429_25 := paid ⟨5,6,2⟩ prefix_5_6 84 50 78 [619634784055]
private def p2429_26 := paid ⟨6,6,2⟩ prefix_6_6 84 50 80 [575896213214]
private def p2429_27 := paid ⟨7,6,2⟩ prefix_7_6 84 50 82 [533661560706]
private def p2429_28 := paid ⟨8,6,2⟩ prefix_8_6 84 50 85 [481737194288]
private def p2429_29 := paid ⟨9,6,2⟩ prefix_9_6 84 50 87 [443124352881]
private def p2429_30 := paid ⟨10,6,2⟩ prefix_10_6 84 50 90 [396181461104]
private def p2429_31 := paid ⟨11,6,2⟩ prefix_11_6 84 50 93 [352087556251]
private def p2429_32 := paid ⟨5,6,2⟩ prefix_5_6 87 49 78 [627211435907]
private def p2429_33 := paid ⟨6,6,2⟩ prefix_6_6 87 49 80 [582833138372]
private def p2429_34 := paid ⟨7,6,2⟩ prefix_7_6 87 49 82 [539979580027]
private def p2429_35 := paid ⟨8,6,2⟩ prefix_8_6 87 49 85 [487345787705]
private def p2429_36 := paid ⟨9,6,2⟩ prefix_9_6 87 49 87 [448163520769]
private def p2429_37 := paid ⟨10,6,2⟩ prefix_10_6 87 49 90 [400577392476]
private def p2429_38 := paid ⟨11,6,2⟩ prefix_11_6 87 49 93 [355878269234]
private def p2429_39 := paid ⟨5,6,2⟩ prefix_5_6 91 46 78 [656484105620]
private def p2429_40 := paid ⟨6,6,2⟩ prefix_6_6 91 46 80 [609796317074]
private def p2429_41 := paid ⟨7,6,2⟩ prefix_7_6 91 46 82 [564710070094]
private def p2429_42 := paid ⟨8,6,2⟩ prefix_8_6 91 46 84 [521239516532]
private def p2429_43 := paid ⟨9,6,2⟩ prefix_9_6 91 46 87 [468224742685]
private def p2429_44 := paid ⟨10,6,2⟩ prefix_10_6 91 46 90 [418265074297]
private def p2429_45 := paid ⟨11,6,2⟩ prefix_11_6 91 46 93 [371333856397]
private def p2429_46 := paid ⟨5,6,2⟩ prefix_5_6 93 45 78 [665888626324]
private def p2429_47 := paid ⟨6,6,2⟩ prefix_6_6 93 45 80 [618424586538]
private def p2429_48 := paid ⟨7,6,2⟩ prefix_7_6 93 45 82 [572587487648]
private def p2429_49 := paid ⟨8,6,2⟩ prefix_8_6 93 45 84 [528392101380]
private def p2429_50 := paid ⟨9,6,2⟩ prefix_9_6 93 45 87 [474545154776]
private def p2429_51 := paid ⟨10,6,2⟩ prefix_10_6 93 45 90 [423799745191]
private def p2429_52 := paid ⟨11,6,2⟩ prefix_11_6 93 45 93 [376129393220]
private def p2429_53 := paid ⟨5,6,2⟩ prefix_5_6 93 46 78 [654086373066]
private def p2429_54 := paid ⟨6,6,2⟩ prefix_6_6 93 46 80 [607517657958]
private def p2429_55 := paid ⟨7,6,2⟩ prefix_7_6 93 46 82 [562545705752]
private def p2429_56 := paid ⟨8,6,2⟩ prefix_8_6 93 46 84 [519184814028]
private def p2429_57 := paid ⟨9,6,2⟩ prefix_9_6 93 46 87 [466326162631]
private def p2429_58 := paid ⟨10,6,2⟩ prefix_10_6 93 46 90 [416512982431]
private def p2429_59 := paid ⟨11,6,2⟩ prefix_11_6 93 46 93 [369719067697]
private def p2429_60 := paid ⟨5,6,2⟩ prefix_5_6 93 47 78 [642644942255]
private def p2429_61 := paid ⟨6,6,2⟩ prefix_6_6 93 47 80 [596941308926]
private def p2429_62 := paid ⟨7,6,2⟩ prefix_7_6 93 47 82 [552805070964]
private def p2429_63 := paid ⟨8,6,2⟩ prefix_8_6 93 47 84 [510250201844]
private def p2429_64 := paid ⟨9,6,2⟩ prefix_9_6 93 47 87 [458347625927]
private def p2429_65 := paid ⟨10,6,2⟩ prefix_10_6 93 47 90 [409436323739]
private def p2429_66 := paid ⟨11,6,2⟩ prefix_11_6 93 47 93 [363490101635]
private def p2429_67 := paid ⟨5,6,2⟩ prefix_5_6 94 45 78 [664642132418]
private def p2429_68 := paid ⟨6,6,2⟩ prefix_6_6 94 45 80 [617239990048]
private def p2429_69 := paid ⟨7,6,2⟩ prefix_7_6 94 45 82 [571462306943]
private def p2429_70 := paid ⟨8,6,2⟩ prefix_8_6 94 45 84 [527323928912]
private def p2429_71 := paid ⟨9,6,2⟩ prefix_9_6 94 45 87 [473558139901]
private def p2429_72 := paid ⟨10,6,2⟩ prefix_10_6 94 45 90 [422888880434]
private def p2429_73 := paid ⟨11,6,2⟩ prefix_11_6 94 45 93 [375289906770]
private def p2429_74 := paid ⟨5,6,2⟩ prefix_5_6 95 46 78 [651688640512]
private def p2429_75 := paid ⟨6,6,2⟩ prefix_6_6 95 46 80 [605238998842]
private def p2429_76 := paid ⟨7,6,2⟩ prefix_7_6 95 46 82 [560381341410]
private def p2429_77 := paid ⟨8,6,2⟩ prefix_8_6 95 46 84 [517130111524]
private def p2429_78 := paid ⟨9,6,2⟩ prefix_9_6 95 46 87 [464427582577]
private def p2429_79 := paid ⟨10,6,2⟩ prefix_10_6 95 46 90 [414760890565]
private def p2429_80 := paid ⟨11,6,2⟩ prefix_11_6 95 46 93 [368104278997]
private def p2429_81 := paid ⟨5,6,2⟩ prefix_5_6 99 43 78 [682537589938]
private def p2429_82 := paid ⟨6,6,2⟩ prefix_6_6 99 43 80 [633587270772]
private def p2429_83 := paid ⟨7,6,2⟩ prefix_7_6 99 43 82 [586311814126]
private def p2429_84 := paid ⟨8,6,2⟩ prefix_8_6 99 43 84 [540727237196]
private def p2429_85 := paid ⟨9,6,2⟩ prefix_9_6 99 43 87 [485327633004]
private def p2429_86 := paid ⟨10,6,2⟩ prefix_10_6 99 43 90 [433115228414]
private def p2429_87 := paid ⟨11,6,2⟩ prefix_11_6 99 43 93 [384064683088]
private def p2429_88 := paid ⟨5,6,2⟩ prefix_5_6 105 46 78 [639699977742]
private def p2429_89 := paid ⟨6,6,2⟩ prefix_6_6 105 46 80 [593845703262]
private def p2429_90 := paid ⟨7,6,2⟩ prefix_7_6 105 46 82 [549559519700]
private def p2429_91 := paid ⟨8,6,2⟩ prefix_8_6 105 46 84 [506856599004]
private def p2429_92 := paid ⟨9,6,2⟩ prefix_9_6 105 46 87 [454934682307]
private def p2429_93 := paid ⟨10,6,2⟩ prefix_10_6 105 46 90 [406000431235]
private def p2429_94 := paid ⟨11,6,2⟩ prefix_11_6 105 46 93 [360030335497]
private def p2429_95 := paid ⟨5,6,2⟩ prefix_5_6 110 40 78 [704849270934]
private def p2429_96 := paid ⟨6,6,2⟩ prefix_6_6 110 40 80 [653685186184]
private def p2429_97 := paid ⟨7,6,2⟩ prefix_7_6 110 40 82 [604265859540]
private def p2429_98 := paid ⟨8,6,2⟩ prefix_8_6 110 40 84 [556609563402]
private def p2429_99 := paid ⟨9,6,2⟩ prefix_9_6 110 40 87 [498972088072]
private def p2429_100 := paid ⟨10,6,2⟩ prefix_10_6 110 40 89 [455534598506]
private def p2429_101 := paid ⟨11,6,2⟩ prefix_11_6 110 40 93 [393601947178]
private def p2429_102 := paid ⟨5,6,2⟩ prefix_5_6 115 38 77 [738115096413]
private def p2429_103 := paid ⟨6,6,2⟩ prefix_6_6 115 38 79 [684538276882]
private def p2429_104 := paid ⟨7,6,2⟩ prefix_7_6 115 38 82 [619206265434]
private def p2429_105 := paid ⟨8,6,2⟩ prefix_8_6 115 38 84 [569923713828]
private def p2429_106 := paid ⟨9,6,2⟩ prefix_9_6 115 38 86 [522476434328]
private def p2429_107 := paid ⟨10,6,2⟩ prefix_10_6 115 38 89 [465576474444]
private def p2429_108 := paid ⟨11,6,2⟩ prefix_11_6 115 38 93 [401863986398]
private def p2429_109 := paid ⟨5,6,2⟩ prefix_5_6 118 38 78 [718185839511]
private def p2429_110 := paid ⟨6,6,2⟩ prefix_6_6 118 38 79 [679636412869]
private def p2429_111 := paid ⟨7,6,2⟩ prefix_7_6 118 38 82 [614667520047]
private def p2429_112 := paid ⟨8,6,2⟩ prefix_8_6 118 38 84 [565614848520]
private def p2429_113 := paid ⟨9,6,2⟩ prefix_9_6 118 38 86 [518388043157]
private def p2429_114 := paid ⟨10,6,2⟩ prefix_10_6 118 38 89 [461801808043]
private def p2429_115 := paid ⟨11,6,2⟩ prefix_11_6 118 38 93 [398477681565]
private def p2429_116 := paid ⟨5,6,2⟩ prefix_5_6 120 49 79 [579664560850]
private def p2429_117 := paid ⟨6,6,2⟩ prefix_6_6 120 49 80 [549238068314]
private def p2429_118 := paid ⟨7,6,2⟩ prefix_7_6 120 49 82 [508069830760]
private def p2429_119 := paid ⟨8,6,2⟩ prefix_8_6 120 49 85 [457836668054]
private def p2429_120 := paid ⟨9,6,2⟩ prefix_9_6 120 49 87 [420172939678]
private def p2429_121 := paid ⟨10,6,2⟩ prefix_10_6 120 49 90 [374746791900]
private def p2429_122 := paid ⟨11,6,2⟩ prefix_11_6 120 49 94 [323713331446]
private def p2429_123 := paid ⟨5,6,2⟩ prefix_5_6 122 40 78 [686452298586]
private def p2429_124 := paid ⟨6,6,2⟩ prefix_6_6 122 40 80 [636201566536]
private def p2429_125 := paid ⟨7,6,2⟩ prefix_7_6 122 40 82 [587658948192]
private def p2429_126 := paid ⟨8,6,2⟩ prefix_8_6 122 40 84 [540843839154]
private def p2429_127 := paid ⟨9,6,2⟩ prefix_9_6 122 40 87 [484403947024]
private def p2429_128 := paid ⟨10,6,2⟩ prefix_10_6 122 40 90 [431199338532]
private def p2429_129 := paid ⟨11,6,2⟩ prefix_11_6 122 40 93 [381210879802]
private def p2429_130 := paid ⟨5,6,2⟩ prefix_5_6 123 36 77 [751165527063]
private def p2429_131 := paid ⟨6,6,2⟩ prefix_6_6 123 36 79 [696022561377]
private def p2429_132 := paid ⟨7,6,2⟩ prefix_7_6 123 36 81 [642722829842]
private def p2429_133 := paid ⟨8,6,2⟩ prefix_8_6 123 36 84 [578324040090]
private def p2429_134 := paid ⟨9,6,2⟩ prefix_9_6 123 36 86 [529472698776]
private def p2429_135 := paid ⟨10,6,2⟩ prefix_10_6 123 36 89 [471155731248]
private def p2429_136 := paid ⟨11,6,2⟩ prefix_11_6 123 36 93 [406058398868]
private def p2429_137 := paid ⟨5,6,2⟩ prefix_5_6 123 48 78 [598206334572]
private def p2429_138 := paid ⟨6,6,2⟩ prefix_6_6 123 48 80 [554994642174]
private def p2429_139 := paid ⟨7,6,2⟩ prefix_7_6 123 48 82 [513255723666]
private def p2429_140 := paid ⟨8,6,2⟩ prefix_8_6 123 48 85 [462388916031]
private def p2429_141 := paid ⟨9,6,2⟩ prefix_9_6 123 48 87 [424199169639]
private def p2429_142 := paid ⟨10,6,2⟩ prefix_10_6 123 48 90 [378197793588]
private def p2429_143 := paid ⟨11,6,2⟩ prefix_11_6 123 48 93 [334981694067]
private def p2429_144 := paid ⟨5,6,2⟩ prefix_5_6 123 50 79 [567400466633]
private def p2429_145 := paid ⟨6,6,2⟩ prefix_6_6 123 50 81 [526203476358]
private def p2429_146 := paid ⟨7,6,2⟩ prefix_7_6 123 50 83 [486432853349]
private def p2429_147 := paid ⟨8,6,2⟩ prefix_8_6 123 50 85 [448101977036]
private def p2429_148 := paid ⟨9,6,2⟩ prefix_9_6 123 50 87 [411220040259]
private def p2429_149 := paid ⟨10,6,2⟩ prefix_10_6 123 50 90 [366739286342]
private def p2429_150 := paid ⟨11,6,2⟩ prefix_11_6 123 50 94 [316770405796]
private def p2429_151 := paid ⟨5,6,2⟩ prefix_5_6 124 49 79 [575487104078]
private def p2429_152 := paid ⟨6,6,2⟩ prefix_6_6 124 49 80 [545165938610]
private def p2429_153 := paid ⟨7,6,2⟩ prefix_7_6 124 49 83 [493211264558]
private def p2429_154 := paid ⟨8,6,2⟩ prefix_8_6 124 49 85 [454259805066]
private def p2429_155 := paid ⟨9,6,2⟩ prefix_9_6 124 49 87 [416780141970]
private def p2429_156 := paid ⟨10,6,2⟩ prefix_10_6 124 49 90 [371615810012]
private def p2429_157 := paid ⟨11,6,2⟩ prefix_11_6 124 49 94 [320906044998]
private def p2429_158 := paid ⟨5,6,2⟩ prefix_5_6 126 47 78 [604565973206]
private def p2429_159 := paid ⟨6,6,2⟩ prefix_6_6 126 47 80 [560753413424]
private def p2429_160 := paid ⟨7,6,2⟩ prefix_7_6 126 47 82 [518432405241]
private def p2429_161 := paid ⟨8,6,2⟩ prefix_8_6 126 47 85 [466922678432]
private def p2429_162 := paid ⟨9,6,2⟩ prefix_9_6 126 47 87 [428196183749]
private def p2429_163 := paid ⟨10,6,2⟩ prefix_10_6 126 47 90 [381611337308]
private def p2429_164 := paid ⟨11,6,2⟩ prefix_11_6 126 47 93 [337845816419]
private def p2429_165 := paid ⟨5,6,2⟩ prefix_5_6 126 49 79 [573398375692]
private def p2429_166 := paid ⟨6,6,2⟩ prefix_6_6 126 49 80 [543129873758]
private def p2429_167 := paid ⟨7,6,2⟩ prefix_7_6 126 49 83 [491326850744]
private def p2429_168 := paid ⟨8,6,2⟩ prefix_8_6 126 49 85 [452471373572]
private def p2429_169 := paid ⟨9,6,2⟩ prefix_9_6 126 49 87 [415083743116]
private def p2429_170 := paid ⟨10,6,2⟩ prefix_10_6 126 49 90 [370050319068]
private def p2429_171 := r_two6thinwide_11_95_1
private def p2429_172 := paid ⟨13,6,2⟩ prefix_13_6 107 48 102 [245434999089]
private def p2429_173 := paid ⟨13,6,2⟩ prefix_13_6 123 43 102 [254649193646]
private def p2429_174 := paid ⟨4,7,2⟩ prefix_4_7 105 49 92 [327308179172]
private def p2429_175 := paid ⟨5,7,2⟩ prefix_5_7 105 49 96 [281798707434]
private def p2429_176 := paid ⟨6,7,2⟩ prefix_6_7 105 49 99 [248221222663]
private def p2429_177 := paid ⟨4,7,2⟩ prefix_4_7 109 48 92 [331185436607]
private def p2429_178 := paid ⟨5,7,2⟩ prefix_5_7 109 48 95 [293548384475]
private def p2429_179 := paid ⟨6,7,2⟩ prefix_6_7 109 48 99 [251123252203]
private def p2429_180 := paid ⟨4,7,2⟩ prefix_4_7 113 48 92 [329269522475]
private def p2429_181 := paid ⟨5,7,2⟩ prefix_5_7 113 48 96 [283465320612]
private def p2429_182 := paid ⟨6,7,2⟩ prefix_6_7 113 48 99 [249630097339]
private def p2429_183 := paid ⟨4,7,2⟩ prefix_4_7 116 48 92 [327832586876]
private def p2429_184 := paid ⟨5,7,2⟩ prefix_5_7 116 48 96 [282217267950]
private def p2429_185 := paid ⟨6,7,2⟩ prefix_6_7 116 48 99 [248510231191]
private def p2429_186 := paid ⟨4,7,2⟩ prefix_4_7 117 45 92 [345160886875]
private def p2429_187 := paid ⟨5,7,2⟩ prefix_5_7 117 45 95 [305860266041]
private def p2429_188 := paid ⟨6,7,2⟩ prefix_6_7 117 45 99 [261624937592]
private def p2429_189 := paid ⟨4,7,2⟩ prefix_4_7 118 45 92 [344624765136]
private def p2429_190 := paid ⟨5,7,2⟩ prefix_5_7 118 45 95 [305377726202]
private def p2429_191 := paid ⟨6,7,2⟩ prefix_6_7 118 45 99 [261207091478]
private def p2429_192 := paid ⟨4,7,2⟩ prefix_4_7 121 45 92 [343016399919]
private def p2429_193 := paid ⟨5,7,2⟩ prefix_5_7 121 45 95 [303930106685]
private def p2429_194 := paid ⟨6,7,2⟩ prefix_6_7 121 45 99 [259953553136]
private def p2429_195 := paid ⟨4,7,2⟩ prefix_4_7 121 46 92 [336980288609]
private def p2429_196 := paid ⟨5,7,2⟩ prefix_5_7 121 46 95 [298589783633]
private def p2429_197 := paid ⟨6,7,2⟩ prefix_6_7 121 46 99 [255384821195]
private def p2429_198 := paid ⟨4,7,2⟩ prefix_4_7 122 44 92 [348681935252]
private def p2429_199 := paid ⟨5,7,2⟩ prefix_5_7 122 44 95 [308932697913]
private def p2429_200 := paid ⟨6,7,2⟩ prefix_6_7 122 44 99 [264227566152]
private def p2429_201 := paid ⟨4,7,2⟩ prefix_4_7 124 44 92 [347567041174]
private def p2429_202 := paid ⟨5,7,2⟩ prefix_5_7 124 44 95 [307929226245]
private def p2429_203 := paid ⟨6,7,2⟩ prefix_6_7 124 44 99 [263358616536]
private def p2429_204 := paid ⟨4,7,2⟩ prefix_4_7 129 42 92 [357445729258]
private def p2429_205 := paid ⟨5,7,2⟩ prefix_5_7 129 42 95 [316614314960]
private def p2429_206 := paid ⟨6,7,2⟩ prefix_6_7 129 42 99 [270755087357]

private structure ExtraOrder where
  k : Band
  b : ℕ
  j : ℕ
  q : ℕ
  l : ℕ
  positiveIndex : 0 < (start k).j
  paidMass : availableMass ⟨q,(start k).j,(start k).t⟩ ⟨b,j,0⟩ (l-1) < layerNeed

private def newOrders : List ExtraOrder := [
  ⟨.one4,111,52,3,61,by decide,p2429_0⟩,
  ⟨.one4,111,52,4,62,by decide,p2429_1⟩,
  ⟨.one4,111,52,5,63,by decide,p2429_2⟩,
  ⟨.one4,111,52,6,64,by decide,p2429_3⟩,
  ⟨.one4,111,52,7,65,by decide,p2429_4⟩,
  ⟨.one4,111,52,8,66,by decide,p2429_5⟩,
  ⟨.one4,111,52,9,68,by decide,p2429_6⟩,
  ⟨.one4,111,52,10,69,by decide,p2429_7⟩,
  ⟨.one4,111,52,11,70,by decide,p2429_8⟩,
  ⟨.one4,111,52,12,72,by decide,p2429_9⟩,
  ⟨.one4,111,52,13,73,by decide,p2429_10⟩,
  ⟨.one4,111,52,14,75,by decide,p2429_11⟩,
  ⟨.one4,111,52,15,77,by decide,p2429_12⟩,
  ⟨.one4,111,52,16,79,by decide,p2429_13⟩,
  ⟨.one4,111,52,17,81,by decide,p2429_14⟩,
  ⟨.one4,111,52,18,84,by decide,p2429_15⟩,
  ⟨.one4,111,52,19,87,by decide,p2429_16⟩,
  ⟨.one4,111,52,20,91,by decide,p2429_17⟩,
  ⟨.one4,111,52,21,96,by decide,p2429_18⟩,
  ⟨.one4,111,52,22,102,by decide,p2429_19⟩,
  ⟨.one4,111,52,23,111,by decide,p2429_20⟩,
  ⟨.one4,111,52,24,132,by decide,p2429_21⟩,
  ⟨.two6thin,129,47,3,76,by decide,p2429_22⟩,
  ⟨.two6thin,129,49,3,76,by decide,p2429_23⟩,
  ⟨.two6thin,130,46,3,76,by decide,p2429_24⟩,
  ⟨.two6thinwide,84,50,5,79,by decide,p2429_25⟩,
  ⟨.two6thinwide,84,50,6,81,by decide,p2429_26⟩,
  ⟨.two6thinwide,84,50,7,83,by decide,p2429_27⟩,
  ⟨.two6thinwide,84,50,8,86,by decide,p2429_28⟩,
  ⟨.two6thinwide,84,50,9,88,by decide,p2429_29⟩,
  ⟨.two6thinwide,84,50,10,91,by decide,p2429_30⟩,
  ⟨.two6thinwide,84,50,11,94,by decide,p2429_31⟩,
  ⟨.two6thinwide,87,49,5,79,by decide,p2429_32⟩,
  ⟨.two6thinwide,87,49,6,81,by decide,p2429_33⟩,
  ⟨.two6thinwide,87,49,7,83,by decide,p2429_34⟩,
  ⟨.two6thinwide,87,49,8,86,by decide,p2429_35⟩,
  ⟨.two6thinwide,87,49,9,88,by decide,p2429_36⟩,
  ⟨.two6thinwide,87,49,10,91,by decide,p2429_37⟩,
  ⟨.two6thinwide,87,49,11,94,by decide,p2429_38⟩,
  ⟨.two6thinwide,91,46,5,79,by decide,p2429_39⟩,
  ⟨.two6thinwide,91,46,6,81,by decide,p2429_40⟩,
  ⟨.two6thinwide,91,46,7,83,by decide,p2429_41⟩,
  ⟨.two6thinwide,91,46,8,85,by decide,p2429_42⟩,
  ⟨.two6thinwide,91,46,9,88,by decide,p2429_43⟩,
  ⟨.two6thinwide,91,46,10,91,by decide,p2429_44⟩,
  ⟨.two6thinwide,91,46,11,94,by decide,p2429_45⟩,
  ⟨.two6thinwide,93,45,5,79,by decide,p2429_46⟩,
  ⟨.two6thinwide,93,45,6,81,by decide,p2429_47⟩,
  ⟨.two6thinwide,93,45,7,83,by decide,p2429_48⟩,
  ⟨.two6thinwide,93,45,8,85,by decide,p2429_49⟩,
  ⟨.two6thinwide,93,45,9,88,by decide,p2429_50⟩,
  ⟨.two6thinwide,93,45,10,91,by decide,p2429_51⟩,
  ⟨.two6thinwide,93,45,11,94,by decide,p2429_52⟩,
  ⟨.two6thinwide,93,46,5,79,by decide,p2429_53⟩,
  ⟨.two6thinwide,93,46,6,81,by decide,p2429_54⟩,
  ⟨.two6thinwide,93,46,7,83,by decide,p2429_55⟩,
  ⟨.two6thinwide,93,46,8,85,by decide,p2429_56⟩,
  ⟨.two6thinwide,93,46,9,88,by decide,p2429_57⟩,
  ⟨.two6thinwide,93,46,10,91,by decide,p2429_58⟩,
  ⟨.two6thinwide,93,46,11,94,by decide,p2429_59⟩,
  ⟨.two6thinwide,93,47,5,79,by decide,p2429_60⟩,
  ⟨.two6thinwide,93,47,6,81,by decide,p2429_61⟩,
  ⟨.two6thinwide,93,47,7,83,by decide,p2429_62⟩,
  ⟨.two6thinwide,93,47,8,85,by decide,p2429_63⟩,
  ⟨.two6thinwide,93,47,9,88,by decide,p2429_64⟩,
  ⟨.two6thinwide,93,47,10,91,by decide,p2429_65⟩,
  ⟨.two6thinwide,93,47,11,94,by decide,p2429_66⟩,
  ⟨.two6thinwide,94,45,5,79,by decide,p2429_67⟩,
  ⟨.two6thinwide,94,45,6,81,by decide,p2429_68⟩,
  ⟨.two6thinwide,94,45,7,83,by decide,p2429_69⟩,
  ⟨.two6thinwide,94,45,8,85,by decide,p2429_70⟩,
  ⟨.two6thinwide,94,45,9,88,by decide,p2429_71⟩,
  ⟨.two6thinwide,94,45,10,91,by decide,p2429_72⟩,
  ⟨.two6thinwide,94,45,11,94,by decide,p2429_73⟩,
  ⟨.two6thinwide,95,46,5,79,by decide,p2429_74⟩,
  ⟨.two6thinwide,95,46,6,81,by decide,p2429_75⟩,
  ⟨.two6thinwide,95,46,7,83,by decide,p2429_76⟩,
  ⟨.two6thinwide,95,46,8,85,by decide,p2429_77⟩,
  ⟨.two6thinwide,95,46,9,88,by decide,p2429_78⟩,
  ⟨.two6thinwide,95,46,10,91,by decide,p2429_79⟩,
  ⟨.two6thinwide,95,46,11,94,by decide,p2429_80⟩,
  ⟨.two6thinwide,99,43,5,79,by decide,p2429_81⟩,
  ⟨.two6thinwide,99,43,6,81,by decide,p2429_82⟩,
  ⟨.two6thinwide,99,43,7,83,by decide,p2429_83⟩,
  ⟨.two6thinwide,99,43,8,85,by decide,p2429_84⟩,
  ⟨.two6thinwide,99,43,9,88,by decide,p2429_85⟩,
  ⟨.two6thinwide,99,43,10,91,by decide,p2429_86⟩,
  ⟨.two6thinwide,99,43,11,94,by decide,p2429_87⟩,
  ⟨.two6thinwide,105,46,5,79,by decide,p2429_88⟩,
  ⟨.two6thinwide,105,46,6,81,by decide,p2429_89⟩,
  ⟨.two6thinwide,105,46,7,83,by decide,p2429_90⟩,
  ⟨.two6thinwide,105,46,8,85,by decide,p2429_91⟩,
  ⟨.two6thinwide,105,46,9,88,by decide,p2429_92⟩,
  ⟨.two6thinwide,105,46,10,91,by decide,p2429_93⟩,
  ⟨.two6thinwide,105,46,11,94,by decide,p2429_94⟩,
  ⟨.two6thinwide,110,40,5,79,by decide,p2429_95⟩,
  ⟨.two6thinwide,110,40,6,81,by decide,p2429_96⟩,
  ⟨.two6thinwide,110,40,7,83,by decide,p2429_97⟩,
  ⟨.two6thinwide,110,40,8,85,by decide,p2429_98⟩,
  ⟨.two6thinwide,110,40,9,88,by decide,p2429_99⟩,
  ⟨.two6thinwide,110,40,10,90,by decide,p2429_100⟩,
  ⟨.two6thinwide,110,40,11,94,by decide,p2429_101⟩,
  ⟨.two6thinwide,115,38,5,78,by decide,p2429_102⟩,
  ⟨.two6thinwide,115,38,6,80,by decide,p2429_103⟩,
  ⟨.two6thinwide,115,38,7,83,by decide,p2429_104⟩,
  ⟨.two6thinwide,115,38,8,85,by decide,p2429_105⟩,
  ⟨.two6thinwide,115,38,9,87,by decide,p2429_106⟩,
  ⟨.two6thinwide,115,38,10,90,by decide,p2429_107⟩,
  ⟨.two6thinwide,115,38,11,94,by decide,p2429_108⟩,
  ⟨.two6thinwide,118,38,5,79,by decide,p2429_109⟩,
  ⟨.two6thinwide,118,38,6,80,by decide,p2429_110⟩,
  ⟨.two6thinwide,118,38,7,83,by decide,p2429_111⟩,
  ⟨.two6thinwide,118,38,8,85,by decide,p2429_112⟩,
  ⟨.two6thinwide,118,38,9,87,by decide,p2429_113⟩,
  ⟨.two6thinwide,118,38,10,90,by decide,p2429_114⟩,
  ⟨.two6thinwide,118,38,11,94,by decide,p2429_115⟩,
  ⟨.two6thinwide,120,49,5,80,by decide,p2429_116⟩,
  ⟨.two6thinwide,120,49,6,81,by decide,p2429_117⟩,
  ⟨.two6thinwide,120,49,7,83,by decide,p2429_118⟩,
  ⟨.two6thinwide,120,49,8,86,by decide,p2429_119⟩,
  ⟨.two6thinwide,120,49,9,88,by decide,p2429_120⟩,
  ⟨.two6thinwide,120,49,10,91,by decide,p2429_121⟩,
  ⟨.two6thinwide,120,49,11,95,by decide,p2429_122⟩,
  ⟨.two6thinwide,122,40,5,79,by decide,p2429_123⟩,
  ⟨.two6thinwide,122,40,6,81,by decide,p2429_124⟩,
  ⟨.two6thinwide,122,40,7,83,by decide,p2429_125⟩,
  ⟨.two6thinwide,122,40,8,85,by decide,p2429_126⟩,
  ⟨.two6thinwide,122,40,9,88,by decide,p2429_127⟩,
  ⟨.two6thinwide,122,40,10,91,by decide,p2429_128⟩,
  ⟨.two6thinwide,122,40,11,94,by decide,p2429_129⟩,
  ⟨.two6thinwide,123,36,5,78,by decide,p2429_130⟩,
  ⟨.two6thinwide,123,36,6,80,by decide,p2429_131⟩,
  ⟨.two6thinwide,123,36,7,82,by decide,p2429_132⟩,
  ⟨.two6thinwide,123,36,8,85,by decide,p2429_133⟩,
  ⟨.two6thinwide,123,36,9,87,by decide,p2429_134⟩,
  ⟨.two6thinwide,123,36,10,90,by decide,p2429_135⟩,
  ⟨.two6thinwide,123,36,11,94,by decide,p2429_136⟩,
  ⟨.two6thinwide,123,48,5,79,by decide,p2429_137⟩,
  ⟨.two6thinwide,123,48,6,81,by decide,p2429_138⟩,
  ⟨.two6thinwide,123,48,7,83,by decide,p2429_139⟩,
  ⟨.two6thinwide,123,48,8,86,by decide,p2429_140⟩,
  ⟨.two6thinwide,123,48,9,88,by decide,p2429_141⟩,
  ⟨.two6thinwide,123,48,10,91,by decide,p2429_142⟩,
  ⟨.two6thinwide,123,48,11,94,by decide,p2429_143⟩,
  ⟨.two6thinwide,123,50,5,80,by decide,p2429_144⟩,
  ⟨.two6thinwide,123,50,6,82,by decide,p2429_145⟩,
  ⟨.two6thinwide,123,50,7,84,by decide,p2429_146⟩,
  ⟨.two6thinwide,123,50,8,86,by decide,p2429_147⟩,
  ⟨.two6thinwide,123,50,9,88,by decide,p2429_148⟩,
  ⟨.two6thinwide,123,50,10,91,by decide,p2429_149⟩,
  ⟨.two6thinwide,123,50,11,95,by decide,p2429_150⟩,
  ⟨.two6thinwide,124,49,5,80,by decide,p2429_151⟩,
  ⟨.two6thinwide,124,49,6,81,by decide,p2429_152⟩,
  ⟨.two6thinwide,124,49,7,84,by decide,p2429_153⟩,
  ⟨.two6thinwide,124,49,8,86,by decide,p2429_154⟩,
  ⟨.two6thinwide,124,49,9,88,by decide,p2429_155⟩,
  ⟨.two6thinwide,124,49,10,91,by decide,p2429_156⟩,
  ⟨.two6thinwide,124,49,11,95,by decide,p2429_157⟩,
  ⟨.two6thinwide,126,47,5,79,by decide,p2429_158⟩,
  ⟨.two6thinwide,126,47,6,81,by decide,p2429_159⟩,
  ⟨.two6thinwide,126,47,7,83,by decide,p2429_160⟩,
  ⟨.two6thinwide,126,47,8,86,by decide,p2429_161⟩,
  ⟨.two6thinwide,126,47,9,88,by decide,p2429_162⟩,
  ⟨.two6thinwide,126,47,10,91,by decide,p2429_163⟩,
  ⟨.two6thinwide,126,47,11,94,by decide,p2429_164⟩,
  ⟨.two6thinwide,126,49,5,80,by decide,p2429_165⟩,
  ⟨.two6thinwide,126,49,6,81,by decide,p2429_166⟩,
  ⟨.two6thinwide,126,49,7,84,by decide,p2429_167⟩,
  ⟨.two6thinwide,126,49,8,86,by decide,p2429_168⟩,
  ⟨.two6thinwide,126,49,9,88,by decide,p2429_169⟩,
  ⟨.two6thinwide,126,49,10,91,by decide,p2429_170⟩,
  ⟨.two6thinwide,126,49,11,95,by decide,p2429_171⟩,
  ⟨.two6wide,107,48,13,103,by decide,p2429_172⟩,
  ⟨.two6wide,123,43,13,103,by decide,p2429_173⟩,
  ⟨.two7,105,49,4,93,by decide,p2429_174⟩,
  ⟨.two7,105,49,5,97,by decide,p2429_175⟩,
  ⟨.two7,105,49,6,100,by decide,p2429_176⟩,
  ⟨.two7,109,48,4,93,by decide,p2429_177⟩,
  ⟨.two7,109,48,5,96,by decide,p2429_178⟩,
  ⟨.two7,109,48,6,100,by decide,p2429_179⟩,
  ⟨.two7,113,48,4,93,by decide,p2429_180⟩,
  ⟨.two7,113,48,5,97,by decide,p2429_181⟩,
  ⟨.two7,113,48,6,100,by decide,p2429_182⟩,
  ⟨.two7,116,48,4,93,by decide,p2429_183⟩,
  ⟨.two7,116,48,5,97,by decide,p2429_184⟩,
  ⟨.two7,116,48,6,100,by decide,p2429_185⟩,
  ⟨.two7,117,45,4,93,by decide,p2429_186⟩,
  ⟨.two7,117,45,5,96,by decide,p2429_187⟩,
  ⟨.two7,117,45,6,100,by decide,p2429_188⟩,
  ⟨.two7,118,45,4,93,by decide,p2429_189⟩,
  ⟨.two7,118,45,5,96,by decide,p2429_190⟩,
  ⟨.two7,118,45,6,100,by decide,p2429_191⟩,
  ⟨.two7,121,45,4,93,by decide,p2429_192⟩,
  ⟨.two7,121,45,5,96,by decide,p2429_193⟩,
  ⟨.two7,121,45,6,100,by decide,p2429_194⟩,
  ⟨.two7,121,46,4,93,by decide,p2429_195⟩,
  ⟨.two7,121,46,5,96,by decide,p2429_196⟩,
  ⟨.two7,121,46,6,100,by decide,p2429_197⟩,
  ⟨.two7,122,44,4,93,by decide,p2429_198⟩,
  ⟨.two7,122,44,5,96,by decide,p2429_199⟩,
  ⟨.two7,122,44,6,100,by decide,p2429_200⟩,
  ⟨.two7,124,44,4,93,by decide,p2429_201⟩,
  ⟨.two7,124,44,5,96,by decide,p2429_202⟩,
  ⟨.two7,124,44,6,100,by decide,p2429_203⟩,
  ⟨.two7,129,42,4,93,by decide,p2429_204⟩,
  ⟨.two7,129,42,5,96,by decide,p2429_205⟩,
  ⟨.two7,129,42,6,100,by decide,p2429_206⟩
]

private def findOrder (k : Band) (b j q : ℕ) : List ExtraOrder → ℕ
  | [] => 0
  | entry :: more =>
      if k = entry.k ∧ b = entry.b ∧ j = entry.j ∧ q = entry.q then entry.l
      else findOrder k b j q more

private theorem findOrder_valid (k : Band) (b j t q : ℕ) (entries : List ExtraOrder)
    (h : 0 < findOrder k b j q entries) :
    availableMass ⟨q,(start k).j,(start k).t⟩ ⟨b,j,t⟩
      (findOrder k b j q entries - 1) < layerNeed := by
  induction entries with
  | nil => simp [findOrder] at h
  | cons entry more ih =>
    by_cases he : k = entry.k ∧ b = entry.b ∧ j = entry.j ∧ q = entry.q
    · rw [findOrder, if_pos he]
      rcases he with ⟨hk,hb,hj,hq⟩
      rw [hk,hb,hj,hq]
      have hanti := Final50PriceLayer.availableMass_anti_prefix
        (r := ⟨entry.q,(start entry.k).j,(start entry.k).t⟩)
        (y := ⟨entry.b,entry.j,0⟩) (x := ⟨entry.b,entry.j,t⟩)
        (L := entry.l-1) (Or.inr entry.positiveIndex)
        (entry.positiveIndex.trans_le (Nat.le_add_right _ _)) le_rfl le_rfl
      exact hanti.trans_lt entry.paidMass
    · rw [findOrder, if_neg he] at h ⊢
      exact ih h

def raised (k : Band) (b j t q l : ℕ) : ℕ :=
  max (raisedBefore k b j t q l) (findOrder k b j q newOrders)

theorem raised_pos {k : Band} {b j t q l : ℕ} (h : 0 < l) : 0 < raised k b j t q l :=
  (raisedBefore_pos h).trans_le (le_max_left _ _)

theorem raised_valid (k : Band) (b j t q l : ℕ) :
    raised k b j t q l ≤ l ∨
      availableMass ⟨q,(start k).j,(start k).t⟩ ⟨b,j,t⟩ (raised k b j t q l-1) < layerNeed ∨
        WeightedOrder ⟨q,(start k).j,(start k).t⟩ ⟨b,j,t⟩ (raised k b j t q l) := by
  unfold raised
  by_cases h : findOrder k b j q newOrders ≤ raisedBefore k b j t q l
  · rw [max_eq_left h]
    exact raisedBefore_valid k b j t q l
  · rw [max_eq_right (by omega : raisedBefore k b j t q l ≤ findOrder k b j q newOrders)]
    exact Or.inr (Or.inl (findOrder_valid k b j t q newOrders (by omega)))

#print axioms raised_valid
end Final50PriceActualOrder
