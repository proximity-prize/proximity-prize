import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m0_0 : availableMass (start .empty) ⟨3,9,0⟩ 7 < layerNeed := by
  rw [mass_eq (start .empty) ⟨3,9,0⟩ 7 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 190 [4796260984443, 4063102190709, 3285692264229, 2612641512381, 2036972810301, 1551572984229, 1149192811509, 822447020589, 563814291021, 365637253461, 220122489669, 119340532509, 55225865949, 19576925061, 4056096021, 189858164] (by decide +kernel) (by decide)

private theorem m0_1 : availableMass (start .empty) ⟨4,10,0⟩ 12 < layerNeed := by
  rw [mass_eq (start .empty) ⟨4,10,0⟩ 12 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 177 [4881692334132, 4362275118269, 3454678784497, 2681636560645, 2032695947513, 1497307677901, 1064825716609, 724507260437, 465512738185, 276905810653, 147653370641, 66625542949, 22595684377, 4240383725, 141622099] (by decide +kernel) (by decide)

private theorem m0_2 : availableMass (start .empty) ⟨4,12,0⟩ 13 < layerNeed := by
  rw [mass_eq (start .empty) ⟨4,12,0⟩ 13 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 150 [4881692334132, 4360203959615, 3299120995004, 2421560994236, 1713087887804, 1156684055228, 734901894332, 429863821244, 223262270396, 96359694524, 29988564668, 4551370172, 64081822] (by decide +kernel) (by decide)

private theorem m0_3 : availableMass (start .empty) ⟨10,8,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨10,8,0⟩ 1 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 207 [4481029937559, 3640464436340, 2918998271444, 2307125067060, 1793724797588, 1368215356916, 1020552558420, 741230134964, 521279738900, 352270942068, 226311235796, 136046030900, 74658657684, 35870365940, 13940324948, 3665623476, 381269780, 677332] (by decide +kernel) (by decide)

private theorem m0_4 : availableMass (start .empty) ⟨11,7,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨11,7,0⟩ 1 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 236 [4515035343037, 3736804715014, 3060712102274, 2479371591790, 1983689043850, 1565013661334, 1215137989714, 926297917054, 691172674010, 502884833830, 355000312354, 241528368014, 156921601834, 96075957430, 54330721010, 27468521374, 11715329914, 3740460614, 656570050, 20021810] (by decide +kernel) (by decide)

private theorem m0_5 : availableMass (start .empty) ⟨5,15,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .empty) ⟨5,15,0⟩ 23 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 133 [4881692334132, 4873043834691, 4002303337958, 2778793185818, 1830585596078, 1124696720738, 627092951798, 302690921258, 115357501118, 27909803378, 2115180038, 3463] (by decide +kernel) (by decide)

private theorem m0_6 : availableMass (start .empty) ⟨6,16,0⟩ 26 < layerNeed := by
  rw [mass_eq (start .empty) ⟨6,16,0⟩ 26 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 129 [4881692334132, 4881692334132, 4300840561582, 2945299333036, 1897546038604, 1131751147244, 605061291148, 273717132844, 93053365196, 17498711404, 585007018] (by decide +kernel) (by decide)

private theorem m0_7 : availableMass (start .empty) ⟨6,18,0⟩ 30 < layerNeed := by
  rw [mass_eq (start .empty) ⟨6,18,0⟩ 30 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 121 [4881692334132, 4881692334132, 4632265114002, 3208843596069, 1982603373057, 1113640202493, 543280058649, 210672133461, 52788836529, 4425795117, 353064] (by decide +kernel) (by decide)

private theorem m0_8 : availableMass (start .empty) ⟨18,6,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .empty) ⟨18,6,0⟩ 2 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 277 [4566984148934, 3767323230229, 3069134122153, 2472305759005, 1966566293617, 1542190313893, 1189998842809, 901359338413, 668185693825, 482938237237, 338623731913, 228795376189, 147552803473, 89542082245, 49955716057, 24532643533, 9558767068, 2015546530, 38939808, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_9 : availableMass (start .empty) ⟨19,7,0⟩ 3 < layerNeed := by
  rw [mass_eq (start .empty) ⟨19,7,0⟩ 3 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 238 [4591259976229, 3708408154380, 2939106921144, 2296063006228, 1764658889568, 1331175590364, 982792667080, 707588217444, 494538878448, 333519826348, 215304776664, 131565984180, 74874242944, 38698886268, 17407786728, 6267356164, 1442746523, 70956063, 0, 0] (by decide +kernel) (by decide)

private theorem m0_10 : availableMass (start .empty) ⟨9,27,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .empty) ⟨9,27,0⟩ 38 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 99 [4881692334132, 4881692334132, 4881692334132, 3938208995486, 1979482194492, 796944039288, 214800807084, 22017985368, 24860951] (by decide +kernel) (by decide)

private theorem m0_11 : availableMass (start .empty) ⟨34,5,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .empty) ⟨34,5,0⟩ 2 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 332 [4498024481139, 3538743068123, 2711110666787, 2013405815811, 1432522182395, 956010937739, 572080758759, 270723233873, 66066840505, 2297973417, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_12 : availableMass (start .empty) ⟨34,6,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .empty) ⟨34,6,0⟩ 5 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 280 [4670325862389, 3681682255263, 2776620561123, 2031546565191, 1427682098379, 947368735599, 574067795763, 292408368377, 94529061889, 7201297410, 1102606, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_13 : availableMass (start .empty) ⟨35,7,0⟩ 6 < layerNeed := by
  rw [mass_eq (start .empty) ⟨35,7,0⟩ 6 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 241 [4708198419977, 3669324795333, 2696284441005, 1916056022413, 1302670806501, 831968992821, 481599713533, 231043587268, 66548548471, 3339259481, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_14 : availableMass (start .empty) ⟨35,9,0⟩ 12 < layerNeed := by
  rw [mass_eq (start .empty) ⟨35,9,0⟩ 12 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 195 [4881692334132, 4146532629456, 2954443285884, 2032930074792, 1338537551124, 831544056192, 475961717676, 239536449624, 93759037501, 17063000121, 112081650, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_15 : availableMass (start .empty) ⟨15,44,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨15,44,0⟩ 44 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 81 [4881692334132, 4881692334132, 4881692334132, 4594183352901, 1953961290676, 378798689988, 13638941269] (by decide +kernel) (by decide)

private theorem m0_16 : availableMass (start .empty) ⟨66,4,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,4,0⟩ 1 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 413 [4210242861647, 2832358996204, 1653330103564, 662843227742, 60938705276, 367290, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_17 : availableMass (start .empty) ⟨66,5,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,5,0⟩ 5 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 335 [4580418060207, 3197667745876, 1942814371472, 919831372278, 177584711413, 657679616, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_18 : availableMass (start .empty) ⟨66,6,0⟩ 10 < layerNeed := by
  rw [mass_eq (start .empty) ⟨66,6,0⟩ 10 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 285 [4849321570228, 3743277348973, 2354161208449, 1252447877749, 410919121836, 18052360360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_19 : availableMass (start .empty) ⟨67,7,0⟩ 12 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,7,0⟩ 12 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 247 [4881692334132, 3955196840640, 2464202169132, 1317011204080, 467016091038, 30286960688, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_20 : availableMass (start .empty) ⟨67,9,0⟩ 24 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,9,0⟩ 24 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 207 [4881692334132, 4881692334132, 3873610626480, 2312351730396, 1185018942600, 412958578720, 29004917220, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_21 : availableMass (start .empty) ⟨67,12,0⟩ 26 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,12,0⟩ 26 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 163 [4881692334132, 4881692334132, 4074256002463, 2328491869526, 1149358598966, 419824605615, 50039862312, 595665, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_22 : availableMass (start .empty) ⟨68,15,0⟩ 30 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,15,0⟩ 30 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 140 [4881692334132, 4881692334132, 4526922080086, 2651055609335, 1271211753695, 478926153815, 90595377936, 328680351, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_23 : availableMass (start .empty) ⟨68,16,0⟩ 33 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,16,0⟩ 33 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 136 [4881692334132, 4881692334132, 4775820876245, 3062778215872, 1488969763584, 588164341824, 142728770715, 3860323352, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m0_24 : availableMass (start .empty) ⟨69,21,0⟩ 36 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,21,0⟩ 36 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 114 [4881692334132, 4881692334132, 4881692334132, 3397721566933, 1494443713141, 523930767445, 119293958197, 7080540522, 0, 0] (by decide +kernel) (by decide)

private theorem m0_25 : availableMass (start .empty) ⟨68,23,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,23,0⟩ 37 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 108 [4881692334132, 4881692334132, 4881692334132, 3553010568064, 1511550993173, 507095121925, 110882126797, 8190771093, 0] (by decide +kernel) (by decide)

private theorem m0_26 : availableMass (start .empty) ⟨68,24,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,24,0⟩ 39 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 107 [4881692334132, 4881692334132, 4881692334132, 3928740494829, 1712497609592, 579814542008, 130698995192, 11630749536, 1028791] (by decide +kernel) (by decide)

private theorem m0_27 : availableMass (start .empty) ⟨69,27,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,27,0⟩ 40 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 101 [4881692334132, 4881692334132, 4881692334132, 4050090752410, 1687582146417, 513526537257, 95771820633, 5854673409, 1235461] (by decide +kernel) (by decide)

private theorem m0_28 : availableMass (start .empty) ⟨69,28,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,28,0⟩ 42 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 100 [4881692334132, 4881692334132, 4881692334132, 4371342043944, 1948995095744, 602343597104, 115981280160, 7791195920, 9023791] (by decide +kernel) (by decide)

private theorem m0_29 : availableMass (start .empty) ⟨70,27,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .empty) ⟨70,27,0⟩ 41 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 102 [4881692334132, 4881692334132, 4881692334132, 4222831208955, 1828204441068, 567689455272, 110008392348, 7363869388, 2449202] (by decide +kernel) (by decide)

private theorem m0_30 : availableMass (start .empty) ⟨71,39,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,39,0⟩ 43 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 85 [4881692334132, 4881692334132, 4881692334132, 4418192852085, 1636953669636, 308473533888, 17628915084, 104592] (by decide +kernel) (by decide)

private theorem m0_31 : availableMass (start .empty) ⟨71,43,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,43,0⟩ 44 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 82 [4881692334132, 4881692334132, 4881692334132, 4544813686107, 1683758514163, 270750261499, 9119349309] (by decide +kernel) (by decide)

private theorem m0_32 : availableMass (start .empty) ⟨72,42,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨72,42,0⟩ 44 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 83 [4881692334132, 4881692334132, 4881692334132, 4549398011883, 1713982542577, 289776196213, 11706446741] (by decide +kernel) (by decide)

private theorem m0_33 : availableMass (start .empty) ⟨71,44,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,44,0⟩ 45 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 82 [4881692334132, 4881692334132, 4881692334132, 4672504186886, 1863805941328, 304446270336, 10662410299] (by decide +kernel) (by decide)

private theorem m0_34 : availableMass (start .empty) ⟨72,43,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨72,43,0⟩ 45 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 83 [4881692334132, 4881692334132, 4881692334132, 4675375217691, 1892907575108, 324216036656, 13476829992] (by decide +kernel) (by decide)

private theorem m0_35 : availableMass (start .empty) ⟨71,45,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,45,0⟩ 46 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 82 [4881692334132, 4881692334132, 4881692334132, 4773776510537, 2066594007657, 343623602937, 12604906810] (by decide +kernel) (by decide)

private theorem m0_36 : availableMass (start .empty) ⟨70,48,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨70,48,0⟩ 45 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 79 [4881692334132, 4881692334132, 4881692334132, 4659217439939, 1735007910872, 227030347544, 3308492264] (by decide +kernel) (by decide)

private theorem m0_37 : availableMass (start .empty) ⟨73,49,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨73,49,0⟩ 47 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 80 [4881692334132, 4881692334132, 4881692334132, 4842754050840, 2195182015191, 317675649959, 7056027674] (by decide +kernel) (by decide)

private theorem m0_38 : availableMass (start .empty) ⟨100,30,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨100,30,0⟩ 44 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 99 [4881692334132, 4881692334132, 4881692334132, 4587902827815, 1968459982901, 454511744081, 37101560007, 0, 0] (by decide +kernel) (by decide)

private theorem m0_39 : availableMass (start .empty) ⟨101,35,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,35,0⟩ 45 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 92 [4881692334132, 4881692334132, 4881692334132, 4684851267264, 1991602242469, 396540492165, 26666871749, 0] (by decide +kernel) (by decide)

private theorem m0_40 : availableMass (start .empty) ⟨100,39,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨100,39,0⟩ 45 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 87 [4881692334132, 4881692334132, 4881692334132, 4671615848988, 1864194542963, 316826255987, 15225410555, 1820] (by decide +kernel) (by decide)

private theorem m0_41 : availableMass (start .empty) ⟨101,38,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,38,0⟩ 46 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 89 [4881692334132, 4881692334132, 4881692334132, 4776586302849, 2124683913594, 396567389946, 24104017250, 1332179] (by decide +kernel) (by decide)

private theorem m0_42 : availableMass (start .empty) ⟨101,45,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,45,0⟩ 47 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 83 [4881692334132, 4881692334132, 4881692334132, 4842063450407, 2175672970434, 321340622934, 10322246587] (by decide +kernel) (by decide)

private theorem m0_43 : availableMass (start .empty) ⟨115,36,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨115,36,0⟩ 46 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 91 [4881692334132, 4881692334132, 4881692334132, 4775505980061, 2100665004618, 369790685706, 14431588350, 0] (by decide +kernel) (by decide)

private theorem m0_44 : availableMass (start .empty) ⟨109,43,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨109,43,0⟩ 47 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 85 [4881692334132, 4881692334132, 4881692334132, 4842400177265, 2190824216175, 331664176135, 11570519897, 0] (by decide +kernel) (by decide)

private theorem m0_45 : availableMass (start .empty) ⟨104,53,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .empty) ⟨104,53,0⟩ 48 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 79 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2254721348880, 245015473900, 2456593408] (by decide +kernel) (by decide)

private theorem m0_46 : availableMass (start .empty) ⟨116,42,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨116,42,0⟩ 47 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 86 [4881692334132, 4881692334132, 4881692334132, 4842218182228, 2181726720935, 323748356363, 9922908142, 0] (by decide +kernel) (by decide)

private theorem m0_47 : availableMass (start .empty) ⟨110,52,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .empty) ⟨110,52,0⟩ 48 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 79 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2253988814628, 246843698500, 2789551170] (by decide +kernel) (by decide)

private theorem m0_48 : availableMass (start .empty) ⟨123,41,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨123,41,0⟩ 47 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 87 [4881692334132, 4881692334132, 4881692334132, 4842033805862, 2171468023493, 312925054045, 7301486019, 0] (by decide +kernel) (by decide)

private theorem m0_49 : availableMass (start .empty) ⟨116,51,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .empty) ⟨116,51,0⟩ 48 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 80 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2252605323962, 247466508878, 3013478264] (by decide +kernel) (by decide)

private theorem m0_50 : availableMass (start .empty) ⟨122,50,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .empty) ⟨122,50,0⟩ 48 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 81 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2250550882167, 246739121651, 3051539972] (by decide +kernel) (by decide)

private theorem m0_51 : availableMass (start .empty) ⟨127,49,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .empty) ⟨127,49,0⟩ 48 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 81 [4881692334132, 4881692334132, 4881692334132, 4881692334132, 2252157994210, 247139520950, 2962948374] (by decide +kernel) (by decide)

theorem checked0 (q : Threshold) (hq : q ∈ thresholds .empty) :
    0 < q.j ∧ availableMass (start .empty) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, m0_0⟩
  · exact ⟨by decide, m0_1⟩
  · exact ⟨by decide, m0_2⟩
  · exact ⟨by decide, m0_3⟩
  · exact ⟨by decide, m0_4⟩
  · exact ⟨by decide, m0_5⟩
  · exact ⟨by decide, m0_6⟩
  · exact ⟨by decide, m0_7⟩
  · exact ⟨by decide, m0_8⟩
  · exact ⟨by decide, m0_9⟩
  · exact ⟨by decide, m0_10⟩
  · exact ⟨by decide, m0_11⟩
  · exact ⟨by decide, m0_12⟩
  · exact ⟨by decide, m0_13⟩
  · exact ⟨by decide, m0_14⟩
  · exact ⟨by decide, m0_15⟩
  · exact ⟨by decide, m0_16⟩
  · exact ⟨by decide, m0_17⟩
  · exact ⟨by decide, m0_18⟩
  · exact ⟨by decide, m0_19⟩
  · exact ⟨by decide, m0_20⟩
  · exact ⟨by decide, m0_21⟩
  · exact ⟨by decide, m0_22⟩
  · exact ⟨by decide, m0_23⟩
  · exact ⟨by decide, m0_24⟩
  · exact ⟨by decide, m0_25⟩
  · exact ⟨by decide, m0_26⟩
  · exact ⟨by decide, m0_27⟩
  · exact ⟨by decide, m0_28⟩
  · exact ⟨by decide, m0_29⟩
  · exact ⟨by decide, m0_30⟩
  · exact ⟨by decide, m0_31⟩
  · exact ⟨by decide, m0_32⟩
  · exact ⟨by decide, m0_33⟩
  · exact ⟨by decide, m0_34⟩
  · exact ⟨by decide, m0_35⟩
  · exact ⟨by decide, m0_36⟩
  · exact ⟨by decide, m0_37⟩
  · exact ⟨by decide, m0_38⟩
  · exact ⟨by decide, m0_39⟩
  · exact ⟨by decide, m0_40⟩
  · exact ⟨by decide, m0_41⟩
  · exact ⟨by decide, m0_42⟩
  · exact ⟨by decide, m0_43⟩
  · exact ⟨by decide, m0_44⟩
  · exact ⟨by decide, m0_45⟩
  · exact ⟨by decide, m0_46⟩
  · exact ⟨by decide, m0_47⟩
  · exact ⟨by decide, m0_48⟩
  · exact ⟨by decide, m0_49⟩
  · exact ⟨by decide, m0_50⟩
  · exact ⟨by decide, m0_51⟩

end Low53At2389PriceMass
