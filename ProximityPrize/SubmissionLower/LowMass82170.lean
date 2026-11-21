import ProximityPrize.SubmissionLower.LowCaps82170

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace LowMass82170
open LowCaps82170 (Band start thresholds order)
open LowLayers82170 (layerNeed)
open K1_13 (Shape remaining)
open K1_13_8 (availableMass layerTerm zeroShape fastRemaining)
open K1_13_8_2 (Threshold)
open P0_9_8 (symbol_count)
open private P3_6_8_1.sumBelow P3_6_8_1.sumBelow_eq P3_6_8_1.extend
  from ProximityPrize.SubmissionLower.GoldBranch6N8

private def fastLayer (r y : Shape) (L i : ℕ) :=
  fastRemaining ((i+1)*r.b + (i+1-L)*y.b) ((i+1)*r.j + (i+1-L)*y.j)
private theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  rw [P3_6_8_1.sumBelow_eq, ← K1_13_8.availableMass_eq_sum symbol_count hr hj le_rfl]
  simp only [layerTerm, fastLayer, symbol_count]

local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl

private theorem m0_0 : availableMass (start .empty) (⟨3,9,0⟩ : Shape) 14 < layerNeed := by
  rw [mass_eq (start .empty) (⟨3,9,0⟩ : Shape) 14 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨3,9,0⟩ : Shape) 14) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4560940337870,9468451503326
  have s3 := row! s2,12,36,3726056974632,13194508477958
  have s4 := row! s3,12,48,2992969225932,16187477703890
  have s5 := row! s4,12,60,2361350050224,18548827754114
  have s6 := row! s5,12,72,1824165635604,20372993389718
  have s7 := row! s6,12,84,1374246121272,21747239510990
  have s8 := row! s7,12,96,1004285597532,22751525108522
  have s9 := row! s8,12,108,706842105792,23458367214314
  have s10 := row! s9,12,120,474337638564,23932704852878
  have s11 := row! s10,12,132,299058139464,24231762992342
  have s12 := row! s11,12,144,173153503212,24404916495554
  have s13 := row! s12,12,156,88637575632,24493554071186
  have s14 := row! s13,12,168,37388153652,24530942224838
  have s15 := row! s14,12,180,11146985304,24542089210142
  have s16 := row! s15,12,192,1519769724,24543608979866
  have s17 := row! s16,5,197,12741834,24543621721700
  change P3_6_8_1.sumBelow _ 197 < layerNeed
  rw [s17]
  decide

private theorem m0_1 : availableMass (start .empty) (⟨5,15,0⟩ : Shape) 33 < layerNeed := by
  rw [mass_eq (start .empty) (⟨5,15,0⟩ : Shape) 33 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨5,15,0⟩ : Shape) 33) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4843459789130,14658482120042
  have s4 := row! s3,12,48,3777898524518,18436380644560
  have s5 := row! s4,12,60,2602518127778,21038898772338
  have s6 := row! s5,12,72,1697015885438,22735914657776
  have s7 := row! s6,12,84,1028232989498,23764147647274
  have s8 := row! s7,12,96,561960871958,24326108519232
  have s9 := row! s8,12,108,262941204818,24589049724050
  have s10 := row! s9,12,120,94865900078,24683915624128
  have s11 := row! s10,12,132,20377109738,24704292733866
  have s12 := row! s11,11,143,1067367853,24705360101719
  change P3_6_8_1.sumBelow _ 143 < layerNeed
  rw [s12]
  decide

private theorem m0_2 : availableMass (start .empty) (⟨17,6,0⟩ : Shape) 8 < layerNeed := by
  rw [mass_eq (start .empty) (⟨17,6,0⟩ : Shape) 8 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨17,6,0⟩ : Shape) 8) 0 = 0 := rfl
  have s1 := row! s0,12,12,4846157175588,4846157175588
  have s2 := row! s1,12,24,4171695837452,9017853013040
  have s3 := row! s2,12,36,3431005637228,12448858650268
  have s4 := row! s3,12,48,2793382292492,15242240942760
  have s5 := row! s4,12,60,2248812803564,17491053746324
  have s6 := row! s5,12,72,1787794774028,19278848520352
  have s7 := row! s6,12,84,1401336410732,20680184931084
  have s8 := row! s7,12,96,1080956523788,21761141454872
  have s9 := row! s8,12,108,818684526572,22579825981444
  have s10 := row! s9,12,120,607060435724,23186886417168
  have s11 := row! s10,12,132,439134871148,23626021288316
  have s12 := row! s11,12,144,308469056012,23934490344328
  have s13 := row! s12,12,156,209134816748,24143625161076
  have s14 := row! s13,12,168,135714583052,24279339744128
  have s15 := row! s14,12,180,83301387884,24362641132012
  have s16 := row! s15,12,192,47498867468,24410139999480
  have s17 := row! s16,12,204,24421261292,24434561260772
  have s18 := row! s17,12,216,10693412108,24445254672880
  have s19 := row! s18,12,228,3451177922,24448705850802
  have s20 := row! s19,12,240,446480507,24449152331309
  have s21 := row! s20,12,252,420856,24449152752165
  have s22 := row! s21,12,264,0,24449152752165
  have s23 := row! s22,12,276,0,24449152752165
  have s24 := row! s23,7,283,0,24449152752165
  change P3_6_8_1.sumBelow _ 283 < layerNeed
  rw [s24]
  decide

private theorem m0_3 : availableMass (start .empty) (⟨32,5,0⟩ : Shape) 21 < layerNeed := by
  rw [mass_eq (start .empty) (⟨32,5,0⟩ : Shape) 21 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨32,5,0⟩ : Shape) 21) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4863494209119,9771005374575
  have s3 := row! s2,12,36,4112912014190,13883917388765
  have s4 := row! s3,12,48,3229936811762,17113854200527
  have s5 := row! s4,12,60,2478428098614,19592282299141
  have s6 := row! s5,12,72,1845658132346,21437940431487
  have s7 := row! s6,12,84,1319515202558,22757455634045
  have s8 := row! s7,12,96,888503630850,23645959264895
  have s9 := row! s8,12,108,541743770822,24187703035717
  have s10 := row! s9,12,120,269532614651,24457235650368
  have s11 := row! s10,12,132,77779824529,24535015474897
  have s12 := row! s11,12,144,4597510823,24539612985720
  have s13 := row! s12,12,156,196400,24539613182120
  have s14 := row! s13,12,168,0,24539613182120
  have s15 := row! s14,12,180,0,24539613182120
  have s16 := row! s15,12,192,0,24539613182120
  have s17 := row! s16,12,204,0,24539613182120
  have s18 := row! s17,12,216,0,24539613182120
  have s19 := row! s18,12,228,0,24539613182120
  have s20 := row! s19,12,240,0,24539613182120
  have s21 := row! s20,12,252,0,24539613182120
  have s22 := row! s21,12,264,0,24539613182120
  have s23 := row! s22,12,276,0,24539613182120
  have s24 := row! s23,12,288,0,24539613182120
  have s25 := row! s24,12,300,0,24539613182120
  have s26 := row! s25,12,312,0,24539613182120
  have s27 := row! s26,12,324,0,24539613182120
  have s28 := row! s27,12,336,0,24539613182120
  have s29 := row! s28,12,348,0,24539613182120
  have s30 := row! s29,3,351,0,24539613182120
  change P3_6_8_1.sumBelow _ 351 < layerNeed
  rw [s30]
  decide

private theorem m0_4 : availableMass (start .empty) (⟨13,38,0⟩ : Shape) 50 < layerNeed := by
  rw [mass_eq (start .empty) (⟨13,38,0⟩ : Shape) 50 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨13,38,0⟩ : Shape) 50) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4907511165456,19630044661824
  have s5 := row! s4,12,60,3609480697738,23239525359562
  have s6 := row! s5,12,72,1257110881198,24496636240760
  have s7 := row! s6,12,84,241888700750,24738524941510
  have s8 := row! s7,9,93,8539777312,24747064718822
  change P3_6_8_1.sumBelow _ 93 < layerNeed
  rw [s8]
  decide

private theorem m0_5 : availableMass (start .empty) (⟨62,4,0⟩ : Shape) 37 < layerNeed := by
  rw [mass_eq (start .empty) (⟨62,4,0⟩ : Shape) 37 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨62,4,0⟩ : Shape) 37) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4243740262988,18966273759356
  have s5 := row! s4,12,60,2924548799916,21890822559272
  have s6 := row! s5,12,72,1795314930188,23686137489460
  have s7 := row! s6,12,84,840735605810,24526873095270
  have s8 := row! s7,12,96,148664277962,24675537373232
  have s9 := row! s8,12,108,476337316,24676013710548
  have s10 := row! s9,12,120,0,24676013710548
  have s11 := row! s10,12,132,0,24676013710548
  have s12 := row! s11,12,144,0,24676013710548
  have s13 := row! s12,12,156,0,24676013710548
  have s14 := row! s13,12,168,0,24676013710548
  have s15 := row! s14,12,180,0,24676013710548
  have s16 := row! s15,12,192,0,24676013710548
  have s17 := row! s16,12,204,0,24676013710548
  have s18 := row! s17,12,216,0,24676013710548
  have s19 := row! s18,12,228,0,24676013710548
  have s20 := row! s19,12,240,0,24676013710548
  have s21 := row! s20,12,252,0,24676013710548
  have s22 := row! s21,12,264,0,24676013710548
  have s23 := row! s22,12,276,0,24676013710548
  have s24 := row! s23,12,288,0,24676013710548
  have s25 := row! s24,12,300,0,24676013710548
  have s26 := row! s25,12,312,0,24676013710548
  have s27 := row! s26,12,324,0,24676013710548
  have s28 := row! s27,12,336,0,24676013710548
  have s29 := row! s28,12,348,0,24676013710548
  have s30 := row! s29,12,360,0,24676013710548
  have s31 := row! s30,12,372,0,24676013710548
  have s32 := row! s31,12,384,0,24676013710548
  have s33 := row! s32,12,396,0,24676013710548
  have s34 := row! s33,12,408,0,24676013710548
  have s35 := row! s34,12,420,0,24676013710548
  have s36 := row! s35,12,432,0,24676013710548
  have s37 := row! s36,12,444,0,24676013710548
  have s38 := row! s37,5,449,0,24676013710548
  change P3_6_8_1.sumBelow _ 449 < layerNeed
  rw [s38]
  decide

private theorem m0_6 : availableMass (start .empty) (⟨63,15,0⟩ : Shape) 43 < layerNeed := by
  rw [mass_eq (start .empty) (⟨63,15,0⟩ : Shape) 43 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨63,15,0⟩ : Shape) 43) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4650491354246,19373024850614
  have s5 := row! s4,12,60,2859773004646,22232797855260
  have s6 := row! s5,12,72,1446078676426,23678876531686
  have s7 := row! s6,12,84,610048961566,24288925493252
  have s8 := row! s7,12,96,174487510994,24463413004246
  have s9 := row! s8,12,108,10975666550,24474388670796
  have s10 := row! s9,12,120,0,24474388670796
  have s11 := row! s10,12,132,0,24474388670796
  have s12 := row! s11,12,144,0,24474388670796
  have s13 := row! s12,9,153,0,24474388670796
  change P3_6_8_1.sumBelow _ 153 < layerNeed
  rw [s13]
  decide

private theorem m0_7 : availableMass (start .empty) (⟨65,32,0⟩ : Shape) 50 < layerNeed := by
  rw [mass_eq (start .empty) (⟨65,32,0⟩ : Shape) 50 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨65,32,0⟩ : Shape) 50) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4907511165456,19630044661824
  have s5 := row! s4,12,60,3542877021922,23172921683746
  have s6 := row! s5,12,72,1210778067614,24383699751360
  have s7 := row! s6,12,84,274803482766,24658503234126
  have s8 := row! s7,12,96,26458509950,24684961744076
  have s9 := row! s8,5,101,137600931,24685099345007
  change P3_6_8_1.sumBelow _ 101 < layerNeed
  rw [s9]
  decide

private theorem m0_8 : availableMass (start .empty) (⟨94,38,0⟩ : Shape) 52 < layerNeed := by
  rw [mass_eq (start .empty) (⟨94,38,0⟩ : Shape) 52 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨94,38,0⟩ : Shape) 52) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4907511165456,19630044661824
  have s5 := row! s4,12,60,3788546734108,23418591395932
  have s6 := row! s5,12,72,1041920067711,24460511463643
  have s7 := row! s6,12,84,139034428627,24599545892270
  have s8 := row! s7,11,95,3333569850,24602879462120
  change P3_6_8_1.sumBelow _ 95 < layerNeed
  rw [s8]
  decide

private theorem m1_0 : availableMass (start .one) (⟨2,4,0⟩ : Shape) 3 < layerNeed := by
  rw [mass_eq (start .one) (⟨2,4,0⟩ : Shape) 3 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨2,4,0⟩ : Shape) 3) 0 = 0 := rfl
  have s1 := row! s0,12,12,4611937158459,4611937158459
  have s2 := row! s1,12,24,3942033780912,8553970939371
  have s3 := row! s2,12,36,3332862384428,11886833323799
  have s4 := row! s3,12,48,2789675174912,14676508498711
  have s5 := row! s4,12,60,2308751325996,16985259824707
  have s6 := row! s5,12,72,1886358157232,18871617981939
  have s7 := row! s6,12,84,1518751134092,20390369116031
  have s8 := row! s7,12,96,1202173867968,21592542983999
  have s9 := row! s8,12,108,932858116172,22525401100171
  have s10 := row! s9,12,120,707023781936,23232424882107
  have s11 := row! s10,12,132,520878914412,23753303796519
  have s12 := row! s11,12,144,370619708672,24123923505191
  have s13 := row! s12,12,156,252430505708,24376354010899
  have s14 := row! s13,12,168,162483792432,24538837803331
  have s15 := row! s14,12,180,96940201676,24635778005007
  have s16 := row! s15,12,192,51948512192,24687726517199
  have s17 := row! s16,12,204,23645648652,24711372165851
  have s18 := row! s17,12,216,8156681648,24719528847499
  have s19 := row! s18,12,228,1594827692,24721123675191
  have s20 := row! s19,10,238,61760084,24721185435275
  change P3_6_8_1.sumBelow _ 238 < layerNeed
  rw [s20]
  decide

private theorem m1_1 : availableMass (start .one) (⟨2,6,0⟩ : Shape) 23 < layerNeed := by
  rw [mass_eq (start .one) (⟨2,6,0⟩ : Shape) 23 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨2,6,0⟩ : Shape) 23) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4435722236997,9175727550956
  have s3 := row! s2,12,36,3814075602852,12989803153808
  have s4 := row! s3,12,48,3069285292104,16059088445912
  have s5 := row! s4,12,60,2426736690924,18485825136836
  have s6 := row! s5,12,72,1879411103952,20365236240788
  have s7 := row! s6,12,84,1420153786932,21785390027720
  have s8 := row! s7,12,96,1041673946712,22827063974432
  have s9 := row! s8,12,108,736544741244,23563608715676
  have s10 := row! s9,12,120,497203279584,24060811995260
  have s11 := row! s10,12,132,315950621892,24376762617152
  have s12 := row! s11,12,144,184951779432,24561714396584
  have s13 := row! s12,12,156,96235714572,24657950111156
  have s14 := row! s13,12,168,41695340784,24699645451940
  have s15 := row! s14,12,180,13087522644,24712732974584
  have s16 := row! s15,12,192,2033075832,24714766050416
  have s17 := row! s16,12,204,31884906,24714797935322
  have s18 := row! s17,2,206,0,24714797935322
  change P3_6_8_1.sumBelow _ 206 < layerNeed
  rw [s18]
  decide

private theorem m1_2 : availableMass (start .one) (⟨5,14,0⟩ : Shape) 50 < layerNeed := by
  rw [mass_eq (start .one) (⟨5,14,0⟩ : Shape) 50 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨5,14,0⟩ : Shape) 50) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3876938262239,17208756130844
  have s5 := row! s4,12,60,3187179942809,20395936073653
  have s6 := row! s5,12,72,2028599220491,22424535294144
  have s7 := row! s6,12,84,1184522530731,23609057824875
  have s8 := row! s7,12,96,613283517875,24222341342750
  have s9 := row! s8,12,108,263141508515,24485482851265
  have s10 := row! s9,12,120,80895607035,24566378458300
  have s11 := row! s10,12,132,11884695611,24578263153911
  have s12 := row! s11,12,144,143439450,24578406593361
  have s13 := row! s12,3,147,0,24578406593361
  change P3_6_8_1.sumBelow _ 147 < layerNeed
  rw [s13]
  decide

private theorem m1_3 : availableMass (start .one) (⟨9,25,0⟩ : Shape) 60 < layerNeed := by
  rw [mass_eq (start .one) (⟨9,25,0⟩ : Shape) 60 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨9,25,0⟩ : Shape) 60) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3876938262239,17208756130844
  have s5 := row! s4,12,60,3613962830135,20822718960979
  have s6 := row! s5,12,72,2406055737824,23228774698803
  have s7 := row! s6,12,84,997634073952,24226408772755
  have s8 := row! s7,12,96,285831416800,24512240189555
  have s9 := row! s8,12,108,34742091104,24546982280659
  have s10 := row! s9,10,118,146395002,24547128675661
  change P3_6_8_1.sumBelow _ 118 < layerNeed
  rw [s10]
  decide

private theorem m1_4 : availableMass (start .one) (⟨12,36,0⟩ : Shape) 65 < layerNeed := by
  rw [mass_eq (start .one) (⟨12,36,0⟩ : Shape) 65 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨12,36,0⟩ : Shape) 65) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3876938262239,17208756130844
  have s5 := row! s4,12,60,3613962830135,20822718960979
  have s6 := row! s5,12,72,2863664242925,23686383203904
  have s7 := row! s6,12,84,957692339882,24644075543786
  have s8 := row! s7,12,96,141519686534,24785595230320
  have s9 := row! s8,11,107,1689522376,24787284752696
  change P3_6_8_1.sumBelow _ 107 < layerNeed
  rw [s9]
  decide

private theorem m2_0 : availableMass (start .two) (⟨1,3,0⟩ : Shape) 61 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,3,0⟩ : Shape) 61 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨1,3,0⟩ : Shape) 61) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,3000104969663,15058486486052
  have s5 := row! s4,12,60,2567371549187,17625858035239
  have s6 := row! s5,12,72,2096347002909,19722205038148
  have s7 := row! s6,12,84,1601272799709,21323477837857
  have s8 := row! s7,12,96,1190030437509,22513508275366
  have s9 := row! s8,12,108,855249761301,23368758036667
  have s10 := row! s9,12,120,589424567181,23958182603848
  have s11 := row! s10,12,132,384912602349,24343095206197
  have s12 := row! s11,12,144,233935565109,24577030771306
  have s13 := row! s12,12,156,128579104869,24705609876175
  have s14 := row! s13,12,168,60792822141,24766402698316
  have s15 := row! s14,12,180,22390268541,24788792966857
  have s16 := row! s15,12,192,5048946789,24793841913646
  have s17 := row! s16,12,204,310310709,24794152224355
  have s18 := row! s17,12,216,0,24794152224355
  have s19 := row! s18,12,228,0,24794152224355
  have s20 := row! s19,12,240,0,24794152224355
  have s21 := row! s20,4,244,0,24794152224355
  change P3_6_8_1.sumBelow _ 244 < layerNeed
  rw [s21]
  decide

private theorem m2_1 : availableMass (start .two) (⟨8,23,0⟩ : Shape) 103 < layerNeed := by
  rw [mass_eq (start .two) (⟨8,23,0⟩ : Shape) 103 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨8,23,0⟩ : Shape) 103) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,3000104969663,15058486486052
  have s5 := row! s4,12,60,2567371549187,17625858035239
  have s6 := row! s5,12,72,2177705640359,19803563675598
  have s7 := row! s6,12,84,1829003555243,21632567230841
  have s8 := row! s7,12,96,1519134732047,23151701962888
  have s9 := row! s8,12,108,1156179794574,24307881757462
  have s10 := row! s9,12,120,411968458746,24719850216208
  have s11 := row! s10,12,132,62394600126,24782244816334
  have s12 := row! s11,12,144,852149807,24783096966141
  have s13 := row! s12,12,156,0,24783096966141
  have s14 := row! s13,3,159,0,24783096966141
  change P3_6_8_1.sumBelow _ 159 < layerNeed
  rw [s14]
  decide

private theorem thresholds_valid (k : Band) (q : Threshold) (hq : q ∈ thresholds k) :
    0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  cases k
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m0_0⟩
    · exact ⟨by decide, m0_1⟩
    · exact ⟨by decide, m0_2⟩
    · exact ⟨by decide, m0_3⟩
    · exact ⟨by decide, m0_4⟩
    · exact ⟨by decide, m0_5⟩
    · exact ⟨by decide, m0_6⟩
    · exact ⟨by decide, m0_7⟩
    · exact ⟨by decide, m0_8⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m1_0⟩
    · exact ⟨by decide, m1_1⟩
    · exact ⟨by decide, m1_2⟩
    · exact ⟨by decide, m1_3⟩
    · exact ⟨by decide, m1_4⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨by decide, m2_0⟩
    · exact ⟨by decide, m2_1⟩

theorem order_valid (k : Band) (x : Shape) : order k x = 1 ∨
    availableMass (start k) x (order k x - 1) < layerNeed := by
  rcases (P0_9_8.orderFor_select x.b x.j (thresholds k)).2 with h | ⟨q,hq,hb,hj,he⟩
  · exact Or.inl h
  · right
    change order k x = q.l at he
    rw [he]
    obtain ⟨hpos, hsmall⟩ := thresholds_valid k q hq
    have hr : start k = zeroShape ∨ 0 < (start k).j := by cases k <;> decide
    have hi : 0 < (start k).j + q.j := by omega
    exact (P0_9_8.availableMass_anti_prefix (y := ⟨q.b,q.j,0⟩) hr hi hb hj).trans_lt hsmall
#print axioms order_valid
end LowMass82170
