import ProximityPrize.SubmissionLower.LowCaps82190

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace LowMass82190
open LowCaps82190 (Band start thresholds order)
open LowLayers82190 (layerNeed)
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

private theorem m0_0 : availableMass (start .empty) (⟨3,9,0⟩ : Shape) 10 < layerNeed := by
  rw [mass_eq (start .empty) (⟨3,9,0⟩ : Shape) 10 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨3,9,0⟩ : Shape) 10) 0 = 0 := rfl
  have s1 := row! s0,12,12,4888071006418,4888071006418
  have s2 := row! s1,12,24,4274565471312,9162636477730
  have s3 := row! s2,12,36,3469991518644,12632627996374
  have s4 := row! s3,12,48,2771499764184,15404127760558
  have s5 := row! s4,12,60,2172147095292,17576274855850
  have s6 := row! s5,12,72,1664854350432,19241129206282
  have s7 := row! s6,12,84,1242406319172,20483535525454
  have s8 := row! s7,12,96,897451742184,21380987267638
  have s9 := row! s8,12,108,622503311244,22003490578882
  have s10 := row! s9,12,120,409937669232,22413428248114
  have s11 := row! s10,12,132,251995410132,22665423658246
  have s12 := row! s11,12,144,140781079032,22806204737278
  have s13 := row! s12,12,156,68263172124,22874467909402
  have s14 := row! s13,12,168,26274136704,22900742046106
  have s15 := row! s14,12,180,6510371172,22907252417278
  have s16 := row! s15,12,192,532225032,22907784642310
  have s17 := row! s16,1,193,24238,22907784666548
  change P3_6_8_1.sumBelow _ 193 < layerNeed
  rw [s17]
  decide

private theorem m0_1 : availableMass (start .empty) (⟨5,15,0⟩ : Shape) 29 < layerNeed := by
  rw [mass_eq (start .empty) (⟨5,15,0⟩ : Shape) 29 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨5,15,0⟩ : Shape) 29) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4615512089344,14430534420256
  have s4 := row! s3,12,48,3354114957338,17784649377594
  have s5 := row! s4,12,60,2272313457398,20056962834992
  have s6 := row! s5,12,72,1449453815858,21506416650850
  have s7 := row! s6,12,84,852027304718,22358443955568
  have s8 := row! s7,12,96,445475435978,22803919391546
  have s9 := row! s8,12,108,194189961638,22998109353184
  have s10 := row! s9,12,120,61512873698,23059622226882
  have s11 := row! s10,12,132,9736404158,23069358631040
  have s12 := row! s11,7,139,164415527,23069523046567
  change P3_6_8_1.sumBelow _ 139 < layerNeed
  rw [s12]
  decide

private theorem m0_2 : availableMass (start .empty) (⟨17,6,0⟩ : Shape) 5 < layerNeed := by
  rw [mass_eq (start .empty) (⟨17,6,0⟩ : Shape) 5 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨17,6,0⟩ : Shape) 5) 0 = 0 := rfl
  have s1 := row! s0,12,12,4737670381952,4737670381952
  have s2 := row! s1,12,24,3976293986288,8713964368240
  have s3 := row! s2,12,36,3262337142272,11976301510512
  have s4 := row! s3,12,48,2648896034768,14625197545280
  have s5 := row! s4,12,60,2126085314912,16751282860192
  have s6 := row! s5,12,72,1684530237104,18435813097296
  have s7 := row! s6,12,84,1315366659008,19751179756304
  have s8 := row! s7,12,96,1010241041552,20761420797856
  have s9 := row! s8,12,108,761310448928,21522731246784
  have s10 := row! s9,12,120,561242548592,22083973795376
  have s11 := row! s10,12,132,403215611264,22487189406640
  have s12 := row! s11,12,144,280918510928,22768107917568
  have s13 := row! s12,12,156,188550724832,22956658642400
  have s14 := row! s13,12,168,120822333488,23077480975888
  have s15 := row! s14,12,180,72954020672,23150434996560
  have s16 := row! s15,12,192,40677073424,23191112069984
  have s17 := row! s16,12,204,20233382048,23211345452032
  have s18 := row! s17,12,216,8375440112,23219720892144
  have s19 := row! s18,12,228,2369644278,23222090536422
  have s20 := row! s19,12,240,184424378,23222274960800
  have s21 := row! s20,12,252,1,23222274960801
  have s22 := row! s21,12,264,0,23222274960801
  have s23 := row! s22,12,276,0,23222274960801
  have s24 := row! s23,4,280,0,23222274960801
  change P3_6_8_1.sumBelow _ 280 < layerNeed
  rw [s24]
  decide

private theorem m0_3 : availableMass (start .empty) (⟨9,26,0⟩ : Shape) 41 < layerNeed := by
  rw [mass_eq (start .empty) (⟨9,26,0⟩ : Shape) 41 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨9,26,0⟩ : Shape) 41) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4416608121372,19139141617740
  have s5 := row! s4,12,60,2460779261472,21599920879212
  have s6 := row! s5,12,72,1104678959064,22704599838276
  have s7 := row! s6,12,84,368440092304,23073039930580
  have s8 := row! s7,12,96,65723661384,23138763591964
  have s9 := row! s8,8,104,1781246295,23140544838259
  change P3_6_8_1.sumBelow _ 104 < layerNeed
  rw [s9]
  decide

private theorem m0_4 : availableMass (start .empty) (⟨32,5,0⟩ : Shape) 17 < layerNeed := by
  rw [mass_eq (start .empty) (⟨32,5,0⟩ : Shape) 17 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨32,5,0⟩ : Shape) 17) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4705393762800,9612904928256
  have s3 := row! s2,12,36,3803168544794,13416073473050
  have s4 := row! s3,12,48,2965467725726,16381541198776
  have s5 := row! s4,12,60,2254922367138,18636463565914
  have s6 := row! s5,12,72,1659010070630,20295473636544
  have s7 := row! s6,12,84,1165824469802,21461298106346
  have s8 := row! s7,12,96,764075230254,22225373336600
  have s9 := row! s8,12,108,443090355841,22668463692441
  have s10 := row! s9,12,120,195157128155,22863620820596
  have s11 := row! s10,12,132,39308984020,22902929804616
  have s12 := row! s11,12,144,846322352,22903776126968
  have s13 := row! s12,12,156,0,22903776126968
  have s14 := row! s13,12,168,0,22903776126968
  have s15 := row! s14,12,180,0,22903776126968
  have s16 := row! s15,12,192,0,22903776126968
  have s17 := row! s16,12,204,0,22903776126968
  have s18 := row! s17,12,216,0,22903776126968
  have s19 := row! s18,12,228,0,22903776126968
  have s20 := row! s19,12,240,0,22903776126968
  have s21 := row! s20,12,252,0,22903776126968
  have s22 := row! s21,12,264,0,22903776126968
  have s23 := row! s22,12,276,0,22903776126968
  have s24 := row! s23,12,288,0,22903776126968
  have s25 := row! s24,12,300,0,22903776126968
  have s26 := row! s25,12,312,0,22903776126968
  have s27 := row! s26,12,324,0,22903776126968
  have s28 := row! s27,12,336,0,22903776126968
  have s29 := row! s28,11,347,0,22903776126968
  change P3_6_8_1.sumBelow _ 347 < layerNeed
  rw [s29]
  decide

private theorem m0_5 : availableMass (start .empty) (⟨62,4,0⟩ : Shape) 33 < layerNeed := by
  rw [mass_eq (start .empty) (⟨62,4,0⟩ : Shape) 33 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨62,4,0⟩ : Shape) 33) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4845233400714,14660255731626
  have s4 := row! s3,12,48,3781891110996,18442146842622
  have s5 := row! s4,12,60,2527833036468,20969979879090
  have s6 := row! s5,12,72,1458337299988,22428317179078
  have s7 := row! s6,12,84,564500636218,22992817815296
  have s8 := row! s7,12,96,47358645520,23040176460816
  have s9 := row! s8,12,108,194580,23040176655396
  have s10 := row! s9,12,120,0,23040176655396
  have s11 := row! s10,12,132,0,23040176655396
  have s12 := row! s11,12,144,0,23040176655396
  have s13 := row! s12,12,156,0,23040176655396
  have s14 := row! s13,12,168,0,23040176655396
  have s15 := row! s14,12,180,0,23040176655396
  have s16 := row! s15,12,192,0,23040176655396
  have s17 := row! s16,12,204,0,23040176655396
  have s18 := row! s17,12,216,0,23040176655396
  have s19 := row! s18,12,228,0,23040176655396
  have s20 := row! s19,12,240,0,23040176655396
  have s21 := row! s20,12,252,0,23040176655396
  have s22 := row! s21,12,264,0,23040176655396
  have s23 := row! s22,12,276,0,23040176655396
  have s24 := row! s23,12,288,0,23040176655396
  have s25 := row! s24,12,300,0,23040176655396
  have s26 := row! s25,12,312,0,23040176655396
  have s27 := row! s26,12,324,0,23040176655396
  have s28 := row! s27,12,336,0,23040176655396
  have s29 := row! s28,12,348,0,23040176655396
  have s30 := row! s29,12,360,0,23040176655396
  have s31 := row! s30,12,372,0,23040176655396
  have s32 := row! s31,12,384,0,23040176655396
  have s33 := row! s32,12,396,0,23040176655396
  have s34 := row! s33,12,408,0,23040176655396
  have s35 := row! s34,12,420,0,23040176655396
  have s36 := row! s35,12,432,0,23040176655396
  have s37 := row! s36,12,444,0,23040176655396
  have s38 := row! s37,1,445,0,23040176655396
  change P3_6_8_1.sumBelow _ 445 < layerNeed
  rw [s38]
  decide

private theorem m0_6 : availableMass (start .empty) (⟨65,32,0⟩ : Shape) 46 < layerNeed := by
  rw [mass_eq (start .empty) (⟨65,32,0⟩ : Shape) 46 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨65,32,0⟩ : Shape) 46) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4821360698145,19543894194513
  have s5 := row! s4,12,60,2570651877674,22114546072187
  have s6 := row! s5,12,72,782371227418,22896917299605
  have s7 := row! s6,12,84,144250339594,23041167639199
  have s8 := row! s7,12,96,8094461690,23049262100889
  have s9 := row! s8,1,97,188966,23049262289855
  change P3_6_8_1.sumBelow _ 97 < layerNeed
  rw [s9]
  decide

private theorem m0_7 : availableMass (start .empty) (⟨94,41,0⟩ : Shape) 49 < layerNeed := by
  rw [mass_eq (start .empty) (⟨94,41,0⟩ : Shape) 49 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨94,41,0⟩ : Shape) 49) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4907511165456,19630044661824
  have s5 := row! s4,12,60,2916251584029,22546296245853
  have s6 := row! s5,12,72,599432088693,23145728334546
  have s7 := row! s6,12,84,47197764877,23192926099423
  have s8 := row! s7,5,89,129884520,23193055983943
  change P3_6_8_1.sumBelow _ 89 < layerNeed
  rw [s8]
  decide

private theorem m0_8 : availableMass (start .empty) (⟨115,48,0⟩ : Shape) 50 < layerNeed := by
  rw [mass_eq (start .empty) (⟨115,48,0⟩ : Shape) 50 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨115,48,0⟩ : Shape) 50) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4907511165456,19630044661824
  have s5 := row! s4,12,60,2983617335554,22613661997378
  have s6 := row! s5,12,72,448122878564,23061784875942
  have s7 := row! s6,12,84,14657201348,23076442077290
  change P3_6_8_1.sumBelow _ 84 < layerNeed
  rw [s7]
  decide

private theorem m1_0 : availableMass (start .one) (⟨2,5,0⟩ : Shape) 8 < layerNeed := by
  rw [mass_eq (start .one) (⟨2,5,0⟩ : Shape) 8 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨2,5,0⟩ : Shape) 8) 0 = 0 := rfl
  have s1 := row! s0,12,12,4704990921313,4704990921313
  have s2 := row! s1,12,24,4023338588754,8728329510067
  have s3 := row! s2,12,36,3327761833250,12056091343317
  have s4 := row! s3,12,48,2716440121586,14772531464903
  have s5 := row! s4,12,60,2184191960514,16956723425417
  have s6 := row! s5,12,72,1725779233682,18682502659099
  have s7 := row! s6,12,84,1335907201634,20018409860733
  have s8 := row! s7,12,96,1009224501810,21027634362543
  have s9 := row! s8,12,108,740323148546,21767957511089
  have s10 := row! s9,12,120,523738533074,22291696044163
  have s11 := row! s10,12,132,353949423522,22645645467685
  have s12 := row! s11,12,144,225377964914,22871023432599
  have s13 := row! s12,12,156,132389679170,23003413111769
  have s14 := row! s13,12,168,69293465106,23072706576875
  have s15 := row! s14,12,180,30341598434,23103048175309
  have s16 := row! s15,12,192,9729731762,23112777907071
  have s17 := row! s16,12,204,1596894594,23114374801665
  have s18 := row! s17,10,214,31799947,23114406601612
  change P3_6_8_1.sumBelow _ 214 < layerNeed
  rw [s18]
  decide

private theorem m1_1 : availableMass (start .one) (⟨2,6,0⟩ : Shape) 16 < layerNeed := by
  rw [mass_eq (start .one) (⟨2,6,0⟩ : Shape) 16 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨2,6,0⟩ : Shape) 16) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4297384678209,9037389992168
  have s3 := row! s2,12,36,3511843606632,12549233598800
  have s4 := row! s3,12,48,2807639290452,15356872889252
  have s5 := row! s4,12,60,2202963357504,17559836246756
  have s6 := row! s5,12,72,1690744204524,19250580451280
  have s7 := row! s6,12,84,1263774179352,20514354630632
  have s8 := row! s7,12,96,914709580932,21429064211564
  have s9 := row! s8,12,108,636070659312,22065134870876
  have s10 := row! s9,12,120,420241615644,22485376486520
  have s11 := row! s10,12,132,259470602184,22744847088704
  have s12 := row! s11,12,144,145869722292,22890716810996
  have s13 := row! s12,12,156,71415030432,22962131841428
  have s14 := row! s13,12,168,27946532172,22990078373600
  have s15 := row! s14,12,180,7168184184,22997246557784
  have s16 := row! s15,12,192,647894244,22997894452028
  have s17 := row! s16,7,199,186938,22997894638966
  change P3_6_8_1.sumBelow _ 199 < layerNeed
  rw [s17]
  decide

private theorem m1_2 : availableMass (start .one) (⟨3,9,0⟩ : Shape) 32 < layerNeed := by
  rw [mass_eq (start .one) (⟨3,9,0⟩ : Shape) 32 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨3,9,0⟩ : Shape) 32) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4095418931942,13275133456164
  have s4 := row! s3,12,48,3219125201588,16494258657752
  have s5 := row! s4,12,60,2356295261492,18850553919244
  have s6 := row! s5,12,72,1661150503604,20511704422848
  have s7 := row! s6,12,84,1116637475636,21628341898484
  have s8 := row! s7,12,96,705272743604,22333614642088
  have s9 := row! s8,12,108,409142891828,22742757533916
  have s10 := row! s9,12,120,209904522932,22952662056848
  have s11 := row! s10,12,132,88784257844,23041446314692
  have s12 := row! s11,12,144,26578735796,23068025050488
  have s13 := row! s12,12,156,3654614324,23071679664812
  have s14 := row! s13,12,168,31891402,23071711556214
  have s15 := row! s14,1,169,0,23071711556214
  change P3_6_8_1.sumBelow _ 169 < layerNeed
  rw [s15]
  decide

private theorem m1_3 : availableMass (start .one) (⟨5,14,0⟩ : Shape) 44 < layerNeed := by
  rw [mass_eq (start .one) (⟨5,14,0⟩ : Shape) 44 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨5,14,0⟩ : Shape) 44) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3793201900554,17125019769159
  have s5 := row! s4,12,60,2672602663605,19797622432764
  have s6 := row! s5,12,72,1644563575085,21442186007849
  have s7 := row! s6,12,84,919082283725,22361268291574
  have s8 := row! s7,12,96,445283063061,22806551354635
  have s9 := row! s8,12,108,170829964421,22977381319056
  have s10 := row! s9,12,120,41926816925,23019308135981
  have s11 := row! s10,12,132,3317227485,23022625363466
  have s12 := row! s11,9,141,54922,23022625418388
  change P3_6_8_1.sumBelow _ 141 < layerNeed
  rw [s12]
  decide

private theorem m1_4 : availableMass (start .one) (⟨9,25,0⟩ : Shape) 55 < layerNeed := by
  rw [mass_eq (start .one) (⟨9,25,0⟩ : Shape) 55 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨9,25,0⟩ : Shape) 55) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3876938262239,17208756130844
  have s5 := row! s4,12,60,3406572481781,20615328612625
  have s6 := row! s5,12,72,1785999668986,22401328281611
  have s7 := row! s6,12,84,663761111242,23065089392853
  have s8 := row! s7,12,96,151517292698,23216606685551
  have s9 := row! s8,12,108,9551169130,23226157854681
  have s10 := row! s9,5,113,0,23226157854681
  change P3_6_8_1.sumBelow _ 113 < layerNeed
  rw [s10]
  decide

private theorem m1_5 : availableMass (start .one) (⟨61,4,0⟩ : Shape) 45 < layerNeed := by
  rw [mass_eq (start .one) (⟨61,4,0⟩ : Shape) 45 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨61,4,0⟩ : Shape) 45) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3828641962249,17160459830854
  have s5 := row! s4,12,60,2783076335581,19943536166435
  have s6 := row! s5,12,72,1725627124245,21669163290680
  have s7 := row! s6,12,84,929197440237,22598360730917
  have s8 := row! s7,12,96,352819942301,22951180673218
  have s9 := row! s8,12,108,32304193463,22983484866681
  have s10 := row! s9,12,120,0,22983484866681
  have s11 := row! s10,12,132,0,22983484866681
  have s12 := row! s11,12,144,0,22983484866681
  have s13 := row! s12,12,156,0,22983484866681
  have s14 := row! s13,12,168,0,22983484866681
  have s15 := row! s14,12,180,0,22983484866681
  have s16 := row! s15,12,192,0,22983484866681
  have s17 := row! s16,12,204,0,22983484866681
  have s18 := row! s17,12,216,0,22983484866681
  have s19 := row! s18,12,228,0,22983484866681
  have s20 := row! s19,12,240,0,22983484866681
  have s21 := row! s20,12,252,0,22983484866681
  have s22 := row! s21,12,264,0,22983484866681
  have s23 := row! s22,12,276,0,22983484866681
  have s24 := row! s23,4,280,0,22983484866681
  change P3_6_8_1.sumBelow _ 280 < layerNeed
  rw [s24]
  decide

private theorem m2_0 : availableMass (start .two) (⟨1,3,0⟩ : Shape) 40 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,3,0⟩ : Shape) 40 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨1,3,0⟩ : Shape) 40) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,2945375931013,15003757447402
  have s5 := row! s4,12,60,2329094588712,17332852036114
  have s6 := row! s5,12,72,1796947578132,19129799614246
  have s7 := row! s6,12,84,1351663153152,20481462767398
  have s8 := row! s7,12,96,985927845804,21467390613202
  have s9 := row! s8,12,108,692292139224,22159682752426
  have s10 := row! s9,12,120,463170467652,22622853220078
  have s11 := row! s10,12,132,290841216432,22913694436510
  have s12 := row! s11,12,144,167446722012,23081141158522
  have s13 := row! s12,12,156,84993271944,23166134430466
  have s14 := row! s13,12,168,35351104884,23201485535350
  have s15 := row! s14,12,180,10254410592,23211739945942
  have s16 := row! s15,12,192,1301329932,23213041275874
  have s17 := row! s16,12,204,7330268,23213048606142
  have s18 := row! s17,12,216,0,23213048606142
  have s19 := row! s18,7,223,0,23213048606142
  change P3_6_8_1.sumBelow _ 223 < layerNeed
  rw [s19]
  decide

private theorem m2_1 : availableMass (start .two) (⟨5,13,0⟩ : Shape) 79 < layerNeed := by
  rw [mass_eq (start .two) (⟨5,13,0⟩ : Shape) 79 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨5,13,0⟩ : Shape) 79) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,3000104969663,15058486486052
  have s5 := row! s4,12,60,2567371549187,17625858035239
  have s6 := row! s5,12,72,2177705640359,19803563675598
  have s7 := row! s6,12,84,1760217994211,21563781669809
  have s8 := row! s7,12,96,1000195963867,22563977633676
  have s9 := row! s8,12,108,450943914739,23014921548415
  have s10 := row! s9,12,120,152185945547,23167107493962
  have s11 := row! s10,12,132,28083014563,23195190508525
  have s12 := row! s11,12,144,873665308,23196064173833
  have s13 := row! s12,12,156,0,23196064173833
  have s14 := row! s13,9,165,0,23196064173833
  change P3_6_8_1.sumBelow _ 165 < layerNeed
  rw [s14]
  decide

private theorem m2_2 : availableMass (start .two) (⟨65,38,0⟩ : Shape) 91 < layerNeed := by
  rw [mass_eq (start .two) (⟨65,38,0⟩ : Shape) 91 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨65,38,0⟩ : Shape) 91) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,3000104969663,15058486486052
  have s5 := row! s4,12,60,2567371549187,17625858035239
  have s6 := row! s5,12,72,2177705640359,19803563675598
  have s7 := row! s6,12,84,1829003555243,21632567230841
  have s8 := row! s7,12,96,1338625558795,22971192789636
  have s9 := row! s8,12,108,250007718188,23221200507824
  have s10 := row! s9,12,120,4937243614,23226137751438
  have s11 := row! s10,8,128,0,23226137751438
  change P3_6_8_1.sumBelow _ 128 < layerNeed
  rw [s11]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m1_0⟩
    · exact ⟨by decide, m1_1⟩
    · exact ⟨by decide, m1_2⟩
    · exact ⟨by decide, m1_3⟩
    · exact ⟨by decide, m1_4⟩
    · exact ⟨by decide, m1_5⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨by decide, m2_0⟩
    · exact ⟨by decide, m2_1⟩
    · exact ⟨by decide, m2_2⟩

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
end LowMass82190
