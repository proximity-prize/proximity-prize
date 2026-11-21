import ProximityPrize.SubmissionLower.Low48PriceCaps

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Low48PriceMass
open Low48PriceCaps (Band start thresholds order)
open Low48Price (layerNeed)
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

private theorem m0_0 : availableMass (start .empty) (⟨3,9,0⟩ : Shape) 6 < layerNeed := by
  rw [mass_eq (start .empty) (⟨3,9,0⟩ : Shape) 6 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨3,9,0⟩ : Shape) 6) 0 = 0 := rfl
  have s1 := row! s0,12,12,4773316117134,4773316117134
  have s2 := row! s1,12,24,3994164254364,8767480371498
  have s3 := row! s2,12,36,3225714093312,11993194464810
  have s4 := row! s3,12,48,2561046876132,14554241340942
  have s5 := row! s4,12,60,1993174140552,16547415481494
  have s6 := row! s5,12,72,1514971375404,18062386856898
  have s7 := row! s6,12,84,1119178020624,19181564877522
  have s8 := row! s7,12,96,798397467252,19979962344774
  have s9 := row! s8,12,108,545097057432,20525059402206
  have s10 := row! s9,12,120,351608084412,20876667486618
  have s11 := row! s10,12,132,210125792544,21086793279162
  have s12 := row! s11,12,144,112709377284,21199502656446
  have s13 := row! s12,12,156,51281985192,21250784641638
  have s14 := row! s13,12,168,17630713932,21268415355570
  have s15 := row! s14,12,180,3406612272,21271821967842
  have s16 := row! s15,9,189,125643554,21271947611396
  change P3_6_8_1.sumBelow _ 189 < layerNeed
  rw [s16]
  decide

private theorem m0_1 : availableMass (start .empty) (⟨4,12,0⟩ : Shape) 20 < layerNeed := by
  rw [mass_eq (start .empty) (⟨4,12,0⟩ : Shape) 20 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨4,12,0⟩ : Shape) 20) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4822158968988,9729670134444
  have s3 := row! s2,12,36,3895730412212,13625400546656
  have s4 := row! s3,12,48,2911848547124,16537249093780
  have s5 := row! s4,12,60,2106781953716,18644031047496
  have s6 := row! s5,12,72,1463763834164,20107794881660
  have s7 := row! s6,12,84,965597408948,21073392290608
  have s8 := row! s7,12,96,594655916852,21668048207460
  have s9 := row! s8,12,108,332882614964,22000930822424
  have s10 := row! s9,12,120,161790778676,22162721601100
  have s11 := row! s10,12,132,62463701684,22225185302784
  have s12 := row! s11,12,144,15554695988,22240739998772
  have s13 := row! s12,12,156,1287091892,22242027090664
  have s14 := row! s13,1,157,79630,22242027170294
  change P3_6_8_1.sumBelow _ 157 < layerNeed
  rw [s14]
  decide

private theorem m0_2 : availableMass (start .empty) (⟨5,15,0⟩ : Shape) 24 < layerNeed := by
  rw [mass_eq (start .empty) (⟨5,15,0⟩ : Shape) 24 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨5,15,0⟩ : Shape) 24) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4117697930408,13932720261320
  have s4 := row! s3,12,48,2869789950068,16802510211388
  have s5 := row! s4,12,60,1899885801128,18702396012516
  have s6 := row! s5,12,72,1175089115588,19877485128104
  have s7 := row! s6,12,84,661453765448,20538938893552
  have s8 := row! s7,12,96,323983862708,20862922756260
  have s9 := row! s8,12,108,126633759368,20989556515628
  have s10 := row! s9,12,120,32308047428,21021864563056
  have s11 := row! s10,12,132,2861558888,21024726121944
  have s12 := row! s11,2,134,605683,21024726727627
  change P3_6_8_1.sumBelow _ 134 < layerNeed
  rw [s12]
  decide

private theorem m0_3 : availableMass (start .empty) (⟨6,17,0⟩ : Shape) 26 < layerNeed := by
  rw [mass_eq (start .empty) (⟨6,17,0⟩ : Shape) 26 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨6,17,0⟩ : Shape) 26) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4272248312309,14087270643221
  have s4 := row! s3,12,48,2850059774166,16937330417387
  have s5 := row! s4,12,60,1774180647706,18711511065093
  have s6 := row! s5,12,72,1007966053350,19719477118443
  have s7 := row! s6,12,84,500798949690,20220276068133
  have s8 := row! s7,12,96,200602073110,20420878141243
  have s9 := row! s8,12,108,53837937786,20474716079029
  have s10 := row! s9,12,120,5508835686,20480224914715
  have s11 := row! s10,3,123,6364178,20480231278893
  change P3_6_8_1.sumBelow _ 123 < layerNeed
  rw [s11]
  decide

private theorem m0_4 : availableMass (start .empty) (⟨8,24,0⟩ : Shape) 31 < layerNeed := by
  rw [mass_eq (start .empty) (⟨8,24,0⟩ : Shape) 31 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨8,24,0⟩ : Shape) 31) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4659130936588,14474153267500
  have s4 := row! s3,12,48,2896963190648,17371116458148
  have s5 := row! s4,12,60,1458129625784,18829246083932
  have s6 := row! s5,12,72,595155903992,19424401987924
  have s7 := row! s6,12,84,165164681528,19589566669452
  have s8 := row! s7,12,96,18398907512,19607965576964
  have s9 := row! s8,3,99,42170024,19608007746988
  change P3_6_8_1.sumBelow _ 99 < layerNeed
  rw [s9]
  decide

private theorem m0_5 : availableMass (start .empty) (⟨9,27,0⟩ : Shape) 36 < layerNeed := by
  rw [mass_eq (start .empty) (⟨9,27,0⟩ : Shape) 36 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨9,27,0⟩ : Shape) 36) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,3568197554637,18290731051005
  have s5 := row! s4,12,60,1732073735013,20022804786018
  have s6 := row! s5,12,72,663788906709,20686593692727
  have s7 := row! s6,12,84,161491857693,20848085550420
  have s8 := row! s7,12,96,12311415357,20860396965777
  have s9 := row! s8,1,97,24238,20860396990015
  change P3_6_8_1.sumBelow _ 97 < layerNeed
  rw [s9]
  decide

private theorem m0_6 : availableMass (start .empty) (⟨10,28,0⟩ : Shape) 38 < layerNeed := by
  rw [mass_eq (start .empty) (⟨10,28,0⟩ : Shape) 38 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨10,28,0⟩ : Shape) 38) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,3907780403608,18630313899976
  have s5 := row! s4,12,60,1898028658476,20528342558452
  have s6 := row! s5,12,72,722514681804,21250857240256
  have s7 := row! s6,12,84,173660264812,21424517505068
  have s8 := row! s7,12,96,12814101516,21437331606584
  change P3_6_8_1.sumBelow _ 96 < layerNeed
  rw [s8]
  decide

private theorem m0_7 : availableMass (start .empty) (⟨10,30,0⟩ : Shape) 39 < layerNeed := by
  rw [mass_eq (start .empty) (⟨10,30,0⟩ : Shape) 39 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨10,30,0⟩ : Shape) 39) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4030765999656,18753299496024
  have s5 := row! s4,12,60,1895284999241,20648584495265
  have s6 := row! s5,12,72,665813815181,21314398310446
  have s7 := row! s6,12,84,133509652721,21447907963167
  have s8 := row! s7,10,94,5477515555,21453385478722
  change P3_6_8_1.sumBelow _ 94 < layerNeed
  rw [s8]
  decide

private theorem m0_8 : availableMass (start .empty) (⟨11,31,0⟩ : Shape) 40 < layerNeed := by
  rw [mass_eq (start .empty) (⟨11,31,0⟩ : Shape) 40 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨11,31,0⟩ : Shape) 40) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4174339927616,18896873423984
  have s5 := row! s4,12,60,1965527115830,20862400539814
  have s6 := row! s5,12,72,672529897434,21534930437248
  have s7 := row! s6,12,84,127216167734,21662146604982
  have s8 := row! s7,9,93,4271570598,21666418175580
  change P3_6_8_1.sumBelow _ 93 < layerNeed
  rw [s8]
  decide

private theorem m0_9 : availableMass (start .empty) (⟨12,36,0⟩ : Shape) 41 < layerNeed := by
  rw [mass_eq (start .empty) (⟨12,36,0⟩ : Shape) 41 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨12,36,0⟩ : Shape) 41) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4248954442632,18971487939000
  have s5 := row! s4,12,60,1816894413828,20788382352828
  have s6 := row! s5,12,72,484363591812,21272745944640
  have s7 := row! s6,12,84,47779073028,21320525017668
  have s8 := row! s7,2,86,35791398,21320560809066
  change P3_6_8_1.sumBelow _ 86 < layerNeed
  rw [s8]
  decide

private theorem m0_10 : availableMass (start .empty) (⟨17,6,0⟩ : Shape) 2 < layerNeed := by
  rw [mass_eq (start .empty) (⟨17,6,0⟩ : Shape) 2 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨17,6,0⟩ : Shape) 2) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577682559690,4577682559690
  have s2 := row! s1,12,24,3787821622484,8365504182174
  have s3 := row! s2,12,36,3099948387668,11465452569842
  have s4 := row! s3,12,48,2510071683092,13975524252934
  have s5 := row! s4,12,60,2008433810708,15983958063642
  have s6 := row! s5,12,72,1585787675732,17569745739374
  have s7 := row! s6,12,84,1233396786644,18803142526018
  have s8 := row! s7,12,96,943035255188,19746177781206
  have s9 := row! s8,12,108,706987796372,20453165577578
  have s10 := row! s9,12,120,518049728468,20971215306046
  have s11 := row! s10,12,132,369526973012,21340742279058
  have s12 := row! s11,12,144,255236054804,21595978333862
  have s13 := row! s12,12,156,169504101908,21765482435770
  have s14 := row! s13,12,168,107168845652,21872651281422
  have s15 := row! s14,12,180,63578620628,21936229902050
  have s16 := row! s15,12,192,34592364692,21970822266742
  have s17 := row! s16,12,204,16579618964,21987401885706
  have s18 := row! s17,12,216,6420527828,21993822413534
  have s19 := row! s18,12,228,1520085233,21995342498767
  have s20 := row! s19,12,240,54670670,21995397169437
  have s21 := row! s20,12,252,0,21995397169437
  have s22 := row! s21,12,264,0,21995397169437
  have s23 := row! s22,12,276,0,21995397169437
  have s24 := row! s23,1,277,0,21995397169437
  change P3_6_8_1.sumBelow _ 277 < layerNeed
  rw [s24]
  decide

private theorem m0_11 : availableMass (start .empty) (⟨32,5,0⟩ : Shape) 1 < layerNeed := by
  rw [mass_eq (start .empty) (⟨32,5,0⟩ : Shape) 1 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨32,5,0⟩ : Shape) 1) 0 = 0 := rfl
  have s1 := row! s0,12,12,4438740442702,4438740442702
  have s2 := row! s1,12,24,3509008215314,7947748658016
  have s3 := row! s2,12,36,2715121954006,10662870612022
  have s4 := row! s3,12,48,2044148572378,12707019184400
  have s5 := row! s4,12,60,1483771016030,14190790200430
  have s6 := row! s5,12,72,1022288262562,15213078462992
  have s7 := row! s6,12,84,648615321574,15861693784566
  have s8 := row! s7,12,96,352357376172,16214051160738
  have s9 := row! s8,12,108,130534734799,16344585895537
  have s10 := row! s9,12,120,15778212247,16360364107784
  have s11 := row! s10,12,132,63798576,16360427906360
  have s12 := row! s11,12,144,0,16360427906360
  have s13 := row! s12,12,156,0,16360427906360
  have s14 := row! s13,12,168,0,16360427906360
  have s15 := row! s14,12,180,0,16360427906360
  have s16 := row! s15,12,192,0,16360427906360
  have s17 := row! s16,12,204,0,16360427906360
  have s18 := row! s17,12,216,0,16360427906360
  have s19 := row! s18,12,228,0,16360427906360
  have s20 := row! s19,12,240,0,16360427906360
  have s21 := row! s20,12,252,0,16360427906360
  have s22 := row! s21,12,264,0,16360427906360
  have s23 := row! s22,12,276,0,16360427906360
  have s24 := row! s23,12,288,0,16360427906360
  have s25 := row! s24,12,300,0,16360427906360
  have s26 := row! s25,12,312,0,16360427906360
  have s27 := row! s26,12,324,0,16360427906360
  have s28 := row! s27,7,331,0,16360427906360
  change P3_6_8_1.sumBelow _ 331 < layerNeed
  rw [s28]
  decide

private theorem m0_12 : availableMass (start .empty) (⟨32,6,0⟩ : Shape) 4 < layerNeed := by
  rw [mass_eq (start .empty) (⟨32,6,0⟩ : Shape) 4 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨32,6,0⟩ : Shape) 4) 0 = 0 := rfl
  have s1 := row! s0,12,12,4626249913698,4626249913698
  have s2 := row! s1,12,24,3636499477997,8262749391695
  have s3 := row! s2,12,36,2767372794569,11030122186264
  have s4 := row! s3,12,48,2049719414213,13079841600477
  have s5 := row! s4,12,60,1465894722017,14545736322494
  have s6 := row! s5,12,72,999302183453,15545038505947
  have s7 := row! s6,12,84,634393344377,16179431850324
  have s8 := row! s7,12,96,356667850200,16536099700524
  have s9 := row! s8,12,108,153585571891,16689685272415
  have s10 := row! s9,12,120,30097164137,16719782436552
  have s11 := row! s10,12,132,497440476,16720279877028
  have s12 := row! s11,12,144,0,16720279877028
  have s13 := row! s12,12,156,0,16720279877028
  have s14 := row! s13,12,168,0,16720279877028
  have s15 := row! s14,12,180,0,16720279877028
  have s16 := row! s15,12,192,0,16720279877028
  have s17 := row! s16,12,204,0,16720279877028
  have s18 := row! s17,12,216,0,16720279877028
  have s19 := row! s18,12,228,0,16720279877028
  have s20 := row! s19,12,240,0,16720279877028
  have s21 := row! s20,12,252,0,16720279877028
  have s22 := row! s21,12,264,0,16720279877028
  have s23 := row! s22,12,276,0,16720279877028
  have s24 := row! s23,3,279,0,16720279877028
  change P3_6_8_1.sumBelow _ 279 < layerNeed
  rw [s24]
  decide

private theorem m0_13 : availableMass (start .empty) (⟨33,9,0⟩ : Shape) 11 < layerNeed := by
  rw [mass_eq (start .empty) (⟨33,9,0⟩ : Shape) 11 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨33,9,0⟩ : Shape) 11) 0 = 0 := rfl
  have s1 := row! s0,12,12,4897302402457,4897302402457
  have s2 := row! s1,12,24,4055160858621,8952463261078
  have s3 := row! s2,12,36,2909499593829,11861962854907
  have s4 := row! s3,12,48,2020640715429,13882603570336
  have s5 := row! s4,12,60,1347703209789,15230306780125
  have s6 := row! s5,12,72,853297984941,16083604765066
  have s7 := row! s6,12,84,503527870581,16587132635647
  have s8 := row! s7,12,96,267987618069,16855120253716
  have s9 := row! s8,12,108,119763900429,16974884154145
  have s10 := row! s9,12,120,35669283911,17010553438056
  have s11 := row! s10,12,132,2384708315,17012938146371
  have s12 := row! s11,12,144,0,17012938146371
  have s13 := row! s12,12,156,0,17012938146371
  have s14 := row! s13,12,168,0,17012938146371
  have s15 := row! s14,12,180,0,17012938146371
  have s16 := row! s15,12,192,0,17012938146371
  have s17 := row! s16,2,194,0,17012938146371
  change P3_6_8_1.sumBelow _ 194 < layerNeed
  rw [s17]
  decide

private theorem m0_14 : availableMass (start .empty) (⟨62,4,0⟩ : Shape) 1 < layerNeed := by
  rw [mass_eq (start .empty) (⟨62,4,0⟩ : Shape) 1 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨62,4,0⟩ : Shape) 1) 0 = 0 := rfl
  have s1 := row! s0,12,12,4243740262988,4243740262988
  have s2 := row! s1,12,24,2924548799916,7168289062904
  have s3 := row! s2,12,36,1795314930188,8963603993092
  have s4 := row! s3,12,48,840735605810,9804339598902
  have s5 := row! s4,12,60,148664277962,9953003876864
  have s6 := row! s5,12,72,476337316,9953480214180
  have s7 := row! s6,12,84,0,9953480214180
  have s8 := row! s7,12,96,0,9953480214180
  have s9 := row! s8,12,108,0,9953480214180
  have s10 := row! s9,12,120,0,9953480214180
  have s11 := row! s10,12,132,0,9953480214180
  have s12 := row! s11,12,144,0,9953480214180
  have s13 := row! s12,12,156,0,9953480214180
  have s14 := row! s13,12,168,0,9953480214180
  have s15 := row! s14,12,180,0,9953480214180
  have s16 := row! s15,12,192,0,9953480214180
  have s17 := row! s16,12,204,0,9953480214180
  have s18 := row! s17,12,216,0,9953480214180
  have s19 := row! s18,12,228,0,9953480214180
  have s20 := row! s19,12,240,0,9953480214180
  have s21 := row! s20,12,252,0,9953480214180
  have s22 := row! s21,12,264,0,9953480214180
  have s23 := row! s22,12,276,0,9953480214180
  have s24 := row! s23,12,288,0,9953480214180
  have s25 := row! s24,12,300,0,9953480214180
  have s26 := row! s25,12,312,0,9953480214180
  have s27 := row! s26,12,324,0,9953480214180
  have s28 := row! s27,12,336,0,9953480214180
  have s29 := row! s28,12,348,0,9953480214180
  have s30 := row! s29,12,360,0,9953480214180
  have s31 := row! s30,12,372,0,9953480214180
  have s32 := row! s31,12,384,0,9953480214180
  have s33 := row! s32,12,396,0,9953480214180
  have s34 := row! s33,12,408,0,9953480214180
  have s35 := row! s34,5,413,0,9953480214180
  change P3_6_8_1.sumBelow _ 413 < layerNeed
  rw [s35]
  decide

private theorem m0_15 : availableMass (start .empty) (⟨62,5,0⟩ : Shape) 2 < layerNeed := by
  rw [mass_eq (start .empty) (⟨62,5,0⟩ : Shape) 2 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨62,5,0⟩ : Shape) 2) 0 = 0 := rfl
  have s1 := row! s0,12,12,4320930487637,4320930487637
  have s2 := row! s1,12,24,2945542523963,7266473011600
  have s3 := row! s2,12,36,1796916561795,9063389573395
  have s4 := row! s3,12,48,861808210223,9925197783618
  have s5 := row! s4,12,60,178767057969,10103964841587
  have s6 := row! s5,12,72,1149342411,10105114183998
  have s7 := row! s6,12,84,0,10105114183998
  have s8 := row! s7,12,96,0,10105114183998
  have s9 := row! s8,12,108,0,10105114183998
  have s10 := row! s9,12,120,0,10105114183998
  have s11 := row! s10,12,132,0,10105114183998
  have s12 := row! s11,12,144,0,10105114183998
  have s13 := row! s12,12,156,0,10105114183998
  have s14 := row! s13,12,168,0,10105114183998
  have s15 := row! s14,12,180,0,10105114183998
  have s16 := row! s15,12,192,0,10105114183998
  have s17 := row! s16,12,204,0,10105114183998
  have s18 := row! s17,12,216,0,10105114183998
  have s19 := row! s18,12,228,0,10105114183998
  have s20 := row! s19,12,240,0,10105114183998
  have s21 := row! s20,12,252,0,10105114183998
  have s22 := row! s21,12,264,0,10105114183998
  have s23 := row! s22,12,276,0,10105114183998
  have s24 := row! s23,12,288,0,10105114183998
  have s25 := row! s24,12,300,0,10105114183998
  have s26 := row! s25,12,312,0,10105114183998
  have s27 := row! s26,12,324,0,10105114183998
  have s28 := row! s27,8,332,0,10105114183998
  change P3_6_8_1.sumBelow _ 332 < layerNeed
  rw [s28]
  decide

private theorem m0_16 : availableMass (start .empty) (⟨62,6,0⟩ : Shape) 9 < layerNeed := by
  rw [mass_eq (start .empty) (⟨62,6,0⟩ : Shape) 9 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨62,6,0⟩ : Shape) 9) 0 = 0 := rfl
  have s1 := row! s0,12,12,4837505864741,4837505864741
  have s2 := row! s1,12,24,3666450258887,8503956123628
  have s3 := row! s2,12,36,2352852370139,10856808493767
  have s4 := row! s3,12,48,1308809506703,12165618000470
  have s5 := row! s4,12,60,503072439983,12668690440453
  have s6 := row! s5,12,72,45650067033,12714340507486
  have s7 := row! s6,12,84,194580,12714340702066
  have s8 := row! s7,12,96,0,12714340702066
  have s9 := row! s8,12,108,0,12714340702066
  have s10 := row! s9,12,120,0,12714340702066
  have s11 := row! s10,12,132,0,12714340702066
  have s12 := row! s11,12,144,0,12714340702066
  have s13 := row! s12,12,156,0,12714340702066
  have s14 := row! s13,12,168,0,12714340702066
  have s15 := row! s14,12,180,0,12714340702066
  have s16 := row! s15,12,192,0,12714340702066
  have s17 := row! s16,12,204,0,12714340702066
  have s18 := row! s17,12,216,0,12714340702066
  have s19 := row! s18,12,228,0,12714340702066
  have s20 := row! s19,12,240,0,12714340702066
  have s21 := row! s20,12,252,0,12714340702066
  have s22 := row! s21,12,264,0,12714340702066
  have s23 := row! s22,12,276,0,12714340702066
  have s24 := row! s23,8,284,0,12714340702066
  change P3_6_8_1.sumBelow _ 284 < layerNeed
  rw [s24]
  decide

private theorem m0_17 : availableMass (start .empty) (⟨63,9,0⟩ : Shape) 21 < layerNeed := by
  rw [mass_eq (start .empty) (⟨63,9,0⟩ : Shape) 21 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨63,9,0⟩ : Shape) 21) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4825256860898,9732768026354
  have s3 := row! s2,12,36,3485788968174,13218556994528
  have s4 := row! s3,12,48,2081513435874,15300070430402
  have s5 := row! s4,12,60,1071221880894,16371292311296
  have s6 := row! s5,12,72,382265231486,16753557542782
  have s7 := row! s6,12,84,31253681725,16784811224507
  have s8 := row! s7,12,96,0,16784811224507
  have s9 := row! s8,12,108,0,16784811224507
  have s10 := row! s9,12,120,0,16784811224507
  have s11 := row! s10,12,132,0,16784811224507
  have s12 := row! s11,12,144,0,16784811224507
  have s13 := row! s12,12,156,0,16784811224507
  have s14 := row! s13,12,168,0,16784811224507
  have s15 := row! s14,12,180,0,16784811224507
  have s16 := row! s15,12,192,0,16784811224507
  have s17 := row! s16,12,204,0,16784811224507
  change P3_6_8_1.sumBelow _ 204 < layerNeed
  rw [s17]
  decide

private theorem m0_18 : availableMass (start .empty) (⟨64,15,0⟩ : Shape) 36 < layerNeed := by
  rw [mass_eq (start .empty) (⟨64,15,0⟩ : Shape) 36 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨64,15,0⟩ : Shape) 36) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,3660064471059,18382597967427
  have s5 := row! s4,12,60,1937859994779,20320457962206
  have s6 := row! s5,12,72,883038824979,21203496787185
  have s7 := row! s6,12,84,302566038459,21506062825644
  have s8 := row! s7,12,96,41800948643,21547863774287
  have s9 := row! s8,12,108,6405400,21547870179687
  have s10 := row! s9,12,120,0,21547870179687
  have s11 := row! s10,12,132,0,21547870179687
  have s12 := row! s11,12,144,0,21547870179687
  have s13 := row! s12,2,146,0,21547870179687
  change P3_6_8_1.sumBelow _ 146 < layerNeed
  rw [s13]
  decide

private theorem m0_19 : availableMass (start .empty) (⟨65,21,0⟩ : Shape) 38 < layerNeed := by
  rw [mass_eq (start .empty) (⟨65,21,0⟩ : Shape) 38 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨65,21,0⟩ : Shape) 38) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,3833895526959,18556429023327
  have s5 := row! s4,12,60,1783497860115,20339926883442
  have s6 := row! s5,12,72,681742587147,21021669470589
  have s7 := row! s6,12,84,188259670563,21209929141152
  have s8 := row! s7,12,96,24788465413,21234717606565
  have s9 := row! s8,12,108,50115970,21234767722535
  have s10 := row! s9,8,116,0,21234767722535
  change P3_6_8_1.sumBelow _ 116 < layerNeed
  rw [s10]
  decide

private theorem m0_20 : availableMass (start .empty) (⟨65,24,0⟩ : Shape) 39 < layerNeed := by
  rw [mass_eq (start .empty) (⟨65,24,0⟩ : Shape) 39 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨65,24,0⟩ : Shape) 39) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,3947937326844,18670470823212
  have s5 := row! s4,12,60,1744114284200,20414585107412
  have s6 := row! s5,12,72,606493885160,21021078992572
  have s7 := row! s6,12,84,144712554536,21165791547108
  have s8 := row! s7,12,96,15655847528,21181447394636
  have s9 := row! s8,11,107,95186185,21181542580821
  change P3_6_8_1.sumBelow _ 107 < layerNeed
  rw [s9]
  decide

private theorem m0_21 : availableMass (start .empty) (⟨65,31,0⟩ : Shape) 44 < layerNeed := by
  rw [mass_eq (start .empty) (⟨65,31,0⟩ : Shape) 44 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨65,31,0⟩ : Shape) 44) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4636484173034,19359017669402
  have s5 := row! s4,12,60,2200682252468,21559699921870
  have s6 := row! s5,12,72,656050805688,22215750727558
  have s7 := row! s6,12,84,116462871044,22332213598602
  have s8 := row! s7,12,96,5985274904,22338198873506
  have s9 := row! s8,1,97,17506,22338198891012
  change P3_6_8_1.sumBelow _ 97 < layerNeed
  rw [s9]
  decide

private theorem m0_22 : availableMass (start .empty) (⟨66,29,0⟩ : Shape) 44 < layerNeed := by
  rw [mass_eq (start .empty) (⟨66,29,0⟩ : Shape) 44 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨66,29,0⟩ : Shape) 44) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4647095591605,19369629087973
  have s5 := row! s4,12,60,2281843945660,21651473033633
  have s6 := row! s5,12,72,731439648656,22382912682289
  have s7 := row! s6,12,84,150773862652,22533686544941
  have s8 := row! s7,12,96,11885464576,22545572009517
  have s9 := row! s8,4,100,30171447,22545602180964
  change P3_6_8_1.sumBelow _ 100 < layerNeed
  rw [s9]
  decide

private theorem m0_23 : availableMass (start .empty) (⟨67,36,0⟩ : Shape) 45 < layerNeed := by
  rw [mass_eq (start .empty) (⟨67,36,0⟩ : Shape) 45 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨67,36,0⟩ : Shape) 45) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4722662427006,19445195923374
  have s5 := row! s4,12,60,2181764736282,21626960659656
  have s6 := row! s5,12,72,538736546874,22165697206530
  have s7 := row! s6,12,84,62097616218,22227794822748
  have s8 := row! s7,6,90,653917425,22228448740173
  change P3_6_8_1.sumBelow _ 90 < layerNeed
  rw [s8]
  decide

private theorem m0_24 : availableMass (start .empty) (⟨67,38,0⟩ : Shape) 46 < layerNeed := by
  rw [mass_eq (start .empty) (⟨67,38,0⟩ : Shape) 46 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨67,38,0⟩ : Shape) 46) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4809498999857,19532032496225
  have s5 := row! s4,12,60,2330780582380,21862813078605
  have s6 := row! s5,12,72,550501862436,22413314941041
  have s7 := row! s6,12,84,56204703708,22469519644749
  have s8 := row! s7,5,89,305491115,22469825135864
  change P3_6_8_1.sumBelow _ 89 < layerNeed
  rw [s8]
  decide

private theorem m0_25 : availableMass (start .empty) (⟨67,43,0⟩ : Shape) 47 < layerNeed := by
  rw [mass_eq (start .empty) (⟨67,43,0⟩ : Shape) 47 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨67,43,0⟩ : Shape) 47) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4870940797676,19593474294044
  have s5 := row! s4,12,60,2409237757647,22002712051691
  have s6 := row! s5,12,72,479580431671,22482292483362
  have s7 := row! s6,12,84,29868256479,22512160739841
  have s8 := row! s7,1,85,297753,22512161037594
  change P3_6_8_1.sumBelow _ 85 < layerNeed
  rw [s8]
  decide

private theorem m0_26 : availableMass (start .empty) (⟨94,33,0⟩ : Shape) 46 < layerNeed := by
  rw [mass_eq (start .empty) (⟨94,33,0⟩ : Shape) 46 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨94,33,0⟩ : Shape) 46) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4809613748865,19532147245233
  have s5 := row! s4,12,60,2336066469204,21868213714437
  have s6 := row! s5,12,72,560350884840,22428564599277
  have s7 := row! s6,12,84,61253735172,22489818334449
  have s8 := row! s7,12,96,378372382,22490196706831
  change P3_6_8_1.sumBelow _ 96 < layerNeed
  rw [s8]
  decide

private theorem m0_27 : availableMass (start .empty) (⟨94,39,0⟩ : Shape) 47 < layerNeed := by
  rw [mass_eq (start .empty) (⟨94,39,0⟩ : Shape) 47 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨94,39,0⟩ : Shape) 47) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4870351816441,19592885312809
  have s5 := row! s4,12,60,2389060620158,21981945932967
  have s6 := row! s5,12,72,477953078666,22459899011633
  have s7 := row! s6,12,84,35358952478,22495257964111
  have s8 := row! s7,5,89,74990862,22495332954973
  change P3_6_8_1.sumBelow _ 89 < layerNeed
  rw [s8]
  decide

private theorem m0_28 : availableMass (start .empty) (⟨95,38,0⟩ : Shape) 47 < layerNeed := by
  rw [mass_eq (start .empty) (⟨95,38,0⟩ : Shape) 47 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨95,38,0⟩ : Shape) 47) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4870872314225,19593405810593
  have s5 := row! s4,12,60,2414208916468,22007614727061
  have s6 := row! s5,12,72,498629548332,22506244275393
  have s7 := row! s6,12,84,39837966948,22546082242341
  have s8 := row! s7,6,90,123109588,22546205351929
  change P3_6_8_1.sumBelow _ 90 < layerNeed
  rw [s8]
  decide

private theorem m0_29 : availableMass (start .empty) (⟨95,46,0⟩ : Shape) 48 < layerNeed := by
  rw [mass_eq (start .empty) (⟨95,46,0⟩ : Shape) 48 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨95,46,0⟩ : Shape) 48) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4907511165456,19630044661824
  have s5 := row! s4,12,60,2469425650424,22099470312248
  have s6 := row! s5,12,72,390381956816,22489852269064
  have s7 := row! s6,11,83,14730954792,22504583223856
  change P3_6_8_1.sumBelow _ 83 < layerNeed
  rw [s7]
  decide

private theorem m0_30 : availableMass (start .empty) (⟨109,43,0⟩ : Shape) 48 < layerNeed := by
  rw [mass_eq (start .empty) (⟨109,43,0⟩ : Shape) 48 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨109,43,0⟩ : Shape) 48) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4907511165456,19630044661824
  have s5 := row! s4,12,60,2482008123717,22112052785541
  have s6 := row! s5,12,72,402487056957,22514539842498
  have s7 := row! s6,12,84,17079269177,22531619111675
  have s8 := row! s7,2,86,0,22531619111675
  change P3_6_8_1.sumBelow _ 86 < layerNeed
  rw [s8]
  decide

private theorem m0_31 : availableMass (start .empty) (⟨118,49,0⟩ : Shape) 49 < layerNeed := by
  rw [mass_eq (start .empty) (⟨118,49,0⟩ : Shape) 49 (Or.inl rfl) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .empty) (⟨118,49,0⟩ : Shape) 49) 0 = 0 := rfl
  have s1 := row! s0,12,12,4907511165456,4907511165456
  have s2 := row! s1,12,24,4907511165456,9815022330912
  have s3 := row! s2,12,36,4907511165456,14722533496368
  have s4 := row! s3,12,48,4907511165456,19630044661824
  have s5 := row! s4,12,60,2629388336951,22259432998775
  have s6 := row! s5,12,72,338799804311,22598232803086
  have s7 := row! s6,10,82,7283677089,22605516480175
  change P3_6_8_1.sumBelow _ 82 < layerNeed
  rw [s7]
  decide

private theorem m1_0 : availableMass (start .one) (⟨2,5,0⟩ : Shape) 3 < layerNeed := by
  rw [mass_eq (start .one) (⟨2,5,0⟩ : Shape) 3 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨2,5,0⟩ : Shape) 3) 0 = 0 := rfl
  have s1 := row! s0,12,12,4583084299747,4583084299747
  have s2 := row! s1,12,24,3833064805960,8416149105707
  have s3 := row! s2,12,36,3160055470728,11576204576435
  have s4 := row! s3,12,48,2569940874696,14146145451131
  have s5 := row! s4,12,60,2057525884936,16203671336067
  have s6 := row! s5,12,72,1617558745416,17821230081483
  have s7 := row! s6,12,84,1244731077000,19065961158483
  have s8 := row! s7,12,96,933677877448,19999639035931
  have s9 := row! s8,12,108,678977521416,20678616557347
  have s10 := row! s9,12,120,475151760456,21153768317803
  have s11 := row! s10,12,132,316665723016,21470434040819
  have s12 := row! s11,12,144,197927914440,21668361955259
  have s13 := row! s12,12,156,113290216968,21781652172227
  have s14 := row! s13,12,168,57047889736,21838700061963
  have s15 := row! s14,12,180,23439568776,21862139630739
  have s16 := row! s15,12,192,6647267016,21868786897755
  have s17 := row! s16,12,204,796374280,21869583272035
  have s18 := row! s17,5,209,3161993,21869586434028
  change P3_6_8_1.sumBelow _ 209 < layerNeed
  rw [s18]
  decide

private theorem m1_1 : availableMass (start .one) (⟨2,6,0⟩ : Shape) 10 < layerNeed := by
  rw [mass_eq (start .one) (⟨2,6,0⟩ : Shape) 10 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨2,6,0⟩ : Shape) 10) 0 = 0 := rfl
  have s1 := row! s0,12,12,4727530820122,4727530820122
  have s2 := row! s1,12,24,4040037260832,8767568080954
  have s3 := row! s2,12,36,3265619205324,12033187286278
  have s4 := row! s3,12,48,2595368352504,14628555638782
  have s5 := row! s4,12,60,2022303798372,16650859437154
  have s6 := row! s5,12,72,1539308590032,18190168027186
  have s7 := row! s6,12,84,1139129725692,19329297752878
  have s8 := row! s7,12,96,814378154664,20143675907542
  have s9 := row! s8,12,108,557528777364,20701204684906
  have s10 := row! s9,12,120,360920445312,21062125130218
  have s11 := row! s10,12,132,216755961132,21278881091350
  have s12 := row! s11,12,144,117102078552,21395983169902
  have s13 := row! s12,12,156,53889502404,21449872672306
  have s14 := row! s13,12,168,18912888624,21468785560930
  have s15 := row! s14,12,180,3830844252,21472616405182
  have s16 := row! s15,12,192,166228894,21472782634076
  have s17 := row! s16,1,193,0,21472782634076
  change P3_6_8_1.sumBelow _ 193 < layerNeed
  rw [s17]
  decide

private theorem m1_2 : availableMass (start .one) (⟨3,9,0⟩ : Shape) 19 < layerNeed := by
  rw [mass_eq (start .one) (⟨3,9,0⟩ : Shape) 19 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨3,9,0⟩ : Shape) 19) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4351029389498,9091034703457
  have s3 := row! s2,12,36,3400930416878,12491965120335
  have s4 := row! s3,12,48,2504795880734,14996761001069
  have s5 := row! s4,12,60,1779496180046,16776257181115
  have s6 := row! s5,12,72,1208058484094,17984315665209
  have s7 := row! s6,12,84,773079980462,18757395645671
  have s8 := row! s7,12,96,456727875038,19214123520709
  have s9 := row! s8,12,108,240739392014,19454862912723
  have s10 := row! s9,12,120,106421773886,19561284686609
  have s11 := row! s10,12,132,34652281454,19595936968063
  have s12 := row! s11,12,144,5878193822,19601815161885
  have s13 := row! s12,12,156,132798596,19601947960481
  change P3_6_8_1.sumBelow _ 156 < layerNeed
  rw [s13]
  decide

private theorem m1_3 : availableMass (start .one) (⟨4,12,0⟩ : Shape) 37 < layerNeed := by
  rw [mass_eq (start .one) (⟨4,12,0⟩ : Shape) 37 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨4,12,0⟩ : Shape) 37) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3415588961000,16747406829605
  have s5 := row! s4,12,60,2319979594100,19067386423705
  have s6 := row! s5,12,72,1484959965800,20552346389505
  have s7 := row! s6,12,84,877073836100,21429420225605
  have s8 := row! s7,12,96,461815205000,21891235430605
  have s9 := row! s8,12,108,203628312500,22094863743105
  have s10 := row! s9,12,120,65907638600,22160771381705
  have s11 := row! s10,12,132,10997903300,22171769285005
  have s12 := row! s11,12,144,231697700,22172000982705
  have s13 := row! s12,3,147,0,22172000982705
  change P3_6_8_1.sumBelow _ 147 < layerNeed
  rw [s13]
  decide

private theorem m1_4 : availableMass (start .one) (⟨6,17,0⟩ : Shape) 43 < layerNeed := by
  rw [mass_eq (start .one) (⟨6,17,0⟩ : Shape) 43 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨6,17,0⟩ : Shape) 43) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3726303415447,17058121284052
  have s5 := row! s4,12,60,2403960181460,19462081465512
  have s6 := row! s5,12,72,1315214704964,20777296170476
  have s7 := row! s6,12,84,615989511348,21393285681824
  have s8 := row! s7,12,96,222428907812,21615714589636
  have s9 := row! s8,12,108,47801809556,21663516399192
  have s10 := row! s9,12,120,2502090618,21666018489810
  have s11 := row! s10,5,125,0,21666018489810
  change P3_6_8_1.sumBelow _ 125 < layerNeed
  rw [s11]
  decide

private theorem m1_5 : availableMass (start .one) (⟨7,21,0⟩ : Shape) 45 < layerNeed := by
  rw [mass_eq (start .one) (⟨7,21,0⟩ : Shape) 45 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨7,21,0⟩ : Shape) 45) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3802273960002,17134091828607
  have s5 := row! s4,12,60,2393364112304,19527455940911
  have s6 := row! s5,12,72,1143139096688,20670595037599
  have s7 := row! s6,12,84,426338280752,21096933318351
  have s8 := row! s7,12,96,98006075888,21194939394239
  have s9 := row! s8,12,108,6307186352,21201246580591
  have s10 := row! s9,5,113,0,21201246580591
  change P3_6_8_1.sumBelow _ 113 < layerNeed
  rw [s10]
  decide

private theorem m1_6 : availableMass (start .one) (⟨10,30,0⟩ : Shape) 47 < layerNeed := by
  rw [mass_eq (start .one) (⟨10,30,0⟩ : Shape) 47 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨10,30,0⟩ : Shape) 47) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3858989950569,17190807819174
  have s5 := row! s4,12,60,2281873071830,19472680891004
  have s6 := row! s5,12,72,770416307474,20243097198478
  have s7 := row! s6,12,84,140600526638,20383697725116
  have s8 := row! s7,12,96,4105120800,20387802845916
  have s9 := row! s8,1,97,0,20387802845916
  change P3_6_8_1.sumBelow _ 97 < layerNeed
  rw [s9]
  decide

private theorem m1_7 : availableMass (start .one) (⟨62,4,0⟩ : Shape) 1 < layerNeed := by
  rw [mass_eq (start .one) (⟨62,4,0⟩ : Shape) 1 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨62,4,0⟩ : Shape) 1) 0 = 0 := rfl
  have s1 := row! s0,12,12,4104265946104,4104265946104
  have s2 := row! s1,12,24,2642503023260,6746768969364
  have s3 := row! s2,12,36,1510268000824,8257036970188
  have s4 := row! s3,12,48,660393613257,8917430583445
  have s5 := row! s4,12,60,108748390831,9026178974276
  have s6 := row! s5,12,72,164790861,9026343765137
  have s7 := row! s6,12,84,0,9026343765137
  have s8 := row! s7,12,96,0,9026343765137
  have s9 := row! s8,12,108,0,9026343765137
  have s10 := row! s9,12,120,0,9026343765137
  have s11 := row! s10,12,132,0,9026343765137
  have s12 := row! s11,12,144,0,9026343765137
  have s13 := row! s12,12,156,0,9026343765137
  have s14 := row! s13,12,168,0,9026343765137
  have s15 := row! s14,12,180,0,9026343765137
  have s16 := row! s15,12,192,0,9026343765137
  have s17 := row! s16,12,204,0,9026343765137
  have s18 := row! s17,12,216,0,9026343765137
  have s19 := row! s18,12,228,0,9026343765137
  have s20 := row! s19,8,236,0,9026343765137
  change P3_6_8_1.sumBelow _ 236 < layerNeed
  rw [s20]
  decide

private theorem m1_8 : availableMass (start .one) (⟨63,14,0⟩ : Shape) 43 < layerNeed := by
  rw [mass_eq (start .one) (⟨63,14,0⟩ : Shape) 43 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨63,14,0⟩ : Shape) 43) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3676332498326,17008150366931
  have s5 := row! s4,12,60,2087145212533,19095295579464
  have s6 := row! s5,12,72,948372683189,20043668262653
  have s7 := row! s6,12,84,346373544013,20390041806666
  have s8 := row! s7,12,96,81439014561,20471480821227
  have s9 := row! s8,12,108,3832931498,20475313752725
  have s10 := row! s9,12,120,0,20475313752725
  have s11 := row! s10,12,132,0,20475313752725
  have s12 := row! s11,8,140,0,20475313752725
  change P3_6_8_1.sumBelow _ 140 < layerNeed
  rw [s12]
  decide

private theorem m1_9 : availableMass (start .one) (⟨65,25,0⟩ : Shape) 50 < layerNeed := by
  rw [mass_eq (start .one) (⟨65,25,0⟩ : Shape) 50 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨65,25,0⟩ : Shape) 50) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3876938262239,17208756130844
  have s5 := row! s4,12,60,2697050690535,19905806821379
  have s6 := row! s5,12,72,945765591138,20851572412517
  have s7 := row! s6,12,84,226552552274,21078124964791
  have s8 := row! s7,12,96,25263779906,21103388744697
  have s9 := row! s8,12,108,293374812,21103682119509
  change P3_6_8_1.sumBelow _ 108 < layerNeed
  rw [s9]
  decide

private theorem m1_10 : availableMass (start .one) (⟨65,27,0⟩ : Shape) 55 < layerNeed := by
  rw [mass_eq (start .one) (⟨65,27,0⟩ : Shape) 55 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨65,27,0⟩ : Shape) 55) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3876938262239,17208756130844
  have s5 := row! s4,12,60,3330605955975,20539362086819
  have s6 := row! s5,12,72,1391307752563,21930669839382
  have s7 := row! s6,12,84,357370222687,22288040062069
  have s8 := row! s7,12,96,45942095851,22333982157920
  have s9 := row! s8,12,108,825572814,22334807730734
  have s10 := row! s9,2,110,0,22334807730734
  change P3_6_8_1.sumBelow _ 110 < layerNeed
  rw [s10]
  decide

private theorem m1_11 : availableMass (start .one) (⟨65,36,0⟩ : Shape) 58 < layerNeed := by
  rw [mass_eq (start .one) (⟨65,36,0⟩ : Shape) 58 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨65,36,0⟩ : Shape) 58) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3876938262239,17208756130844
  have s5 := row! s4,12,60,3540928695320,20749684826164
  have s6 := row! s5,12,72,1536474012979,22286158839143
  have s7 := row! s6,12,84,279036925627,22565195764770
  have s8 := row! s7,12,96,13277925571,22578473690341
  have s9 := row! s8,4,100,0,22578473690341
  change P3_6_8_1.sumBelow _ 100 < layerNeed
  rw [s9]
  decide

private theorem m1_12 : availableMass (start .one) (⟨66,30,0⟩ : Shape) 56 < layerNeed := by
  rw [mass_eq (start .one) (⟨66,30,0⟩ : Shape) 56 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨66,30,0⟩ : Shape) 56) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3876938262239,17208756130844
  have s5 := row! s4,12,60,3407153525396,20615909656240
  have s6 := row! s5,12,72,1413132153750,22029041809990
  have s7 := row! s6,12,84,320316966090,22349358776080
  have s8 := row! s7,12,96,30036712158,22379395488238
  have s9 := row! s8,10,106,113983282,22379509471520
  change P3_6_8_1.sumBelow _ 106 < layerNeed
  rw [s9]
  decide

private theorem m1_13 : availableMass (start .one) (⟨67,41,0⟩ : Shape) 59 < layerNeed := by
  rw [mass_eq (start .one) (⟨67,41,0⟩ : Shape) 59 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨67,41,0⟩ : Shape) 59) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3876938262239,17208756130844
  have s5 := row! s4,12,60,3586371387357,20795127518201
  have s6 := row! s5,12,72,1577397344638,22372524862839
  have s7 := row! s6,12,84,228437078062,22600961940901
  have s8 := row! s7,12,96,4897904836,22605859845737
  change P3_6_8_1.sumBelow _ 96 < layerNeed
  rw [s8]
  decide

private theorem m1_14 : availableMass (start .one) (⟨94,38,0⟩ : Shape) 59 < layerNeed := by
  rw [mass_eq (start .one) (⟨94,38,0⟩ : Shape) 59 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .one) (⟨94,38,0⟩ : Shape) 59) 0 = 0 := rfl
  have s1 := row! s0,12,12,4740005313959,4740005313959
  have s2 := row! s1,12,24,4439709210263,9179714524222
  have s3 := row! s2,12,36,4152103344383,13331817868605
  have s4 := row! s3,12,48,3876938262239,17208756130844
  have s5 := row! s4,12,60,3585700840592,20794456971436
  have s6 := row! s5,12,72,1556314974252,22350771945688
  have s7 := row! s6,12,84,227238371392,22578010317080
  have s8 := row! s7,12,96,6826338552,22584836655632
  have s9 := row! s8,3,99,0,22584836655632
  change P3_6_8_1.sumBelow _ 99 < layerNeed
  rw [s9]
  decide

private theorem m2_0 : availableMass (start .two) (⟨1,3,0⟩ : Shape) 9 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,3,0⟩ : Shape) 9 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨1,3,0⟩ : Shape) 9) 0 = 0 := rfl
  have s1 := row! s0,12,12,4565332109981,4565332109981
  have s2 := row! s1,12,24,3791944996701,8357277106682
  have s3 := row! s2,12,36,3050088299781,11407365406463
  have s4 := row! s3,12,48,2410280185749,13817645592212
  have s5 := row! s4,12,60,1865498180109,15683143772321
  have s6 := row! s5,12,72,1408583759469,17091727531790
  have s7 := row! s6,12,84,1032242351541,18123969883331
  have s8 := row! s7,12,96,729043335141,18853013218472
  have s9 := row! s8,12,108,491420040189,19344433258661
  have s10 := row! s9,12,120,311669747709,19656103006370
  have s11 := row! s10,12,132,181953689829,19838056696199
  have s12 := row! s11,12,144,94297049781,19932353745980
  have s13 := row! s12,12,156,40588961901,19972942707881
  have s14 := row! s13,12,168,12582511629,19985525219510
  have s15 := row! s14,12,180,1894735509,19987419955019
  have s16 := row! s15,12,192,25840029,19987445795048
  change P3_6_8_1.sumBelow _ 192 < layerNeed
  rw [s16]
  decide

private theorem m2_1 : availableMass (start .two) (⟨2,6,0⟩ : Shape) 29 < layerNeed := by
  rw [mass_eq (start .two) (⟨2,6,0⟩ : Shape) 29 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨2,6,0⟩ : Shape) 29) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3385082572713,11965481373235
  have s4 := row! s3,12,48,2521664745182,14487146118417
  have s5 := row! s4,12,60,1792977610094,16280123728511
  have s6 := row! s5,12,72,1218510466046,17498634194557
  have s7 := row! s6,12,84,780869458574,18279503653131
  have s8 := row! s7,12,96,462230751518,18741734404649
  have s9 := row! s8,12,108,244340527022,18986074931671
  have s10 := row! s9,12,120,108514985534,19094589917205
  have s11 := row! s10,12,132,35640345806,19130230263011
  have s12 := row! s11,12,144,6172844894,19136403107905
  have s13 := row! s12,12,156,151383524,19136554491429
  have s14 := row! s13,10,166,0,19136554491429
  change P3_6_8_1.sumBelow _ 166 < layerNeed
  rw [s14]
  decide

private theorem m2_2 : availableMass (start .two) (⟨3,9,0⟩ : Shape) 61 < layerNeed := by
  rw [mass_eq (start .two) (⟨3,9,0⟩ : Shape) 61 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨3,9,0⟩ : Shape) 61) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,3000104969663,15058486486052
  have s5 := row! s4,12,60,2567371549187,17625858035239
  have s6 := row! s5,12,72,1942282001270,19568140036509
  have s7 := row! s6,12,84,1206027436970,20774167473479
  have s8 := row! s7,12,96,682656446270,21456823919749
  have s9 := row! s8,12,108,337225629170,21794049548919
  have s10 := row! s9,12,120,133741825670,21927791374589
  have s11 := row! s10,12,132,35162115770,21962953490359
  have s12 := row! s11,12,144,3393819470,21966347309829
  have s13 := row! s12,12,156,2172920,21966349482749
  have s14 := row! s13,12,168,0,21966349482749
  have s15 := row! s14,3,171,0,21966349482749
  change P3_6_8_1.sumBelow _ 171 < layerNeed
  rw [s15]
  decide

private theorem m2_3 : availableMass (start .two) (⟨5,14,0⟩ : Shape) 70 < layerNeed := by
  rw [mass_eq (start .two) (⟨5,14,0⟩ : Shape) 70 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨5,14,0⟩ : Shape) 70) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,3000104969663,15058486486052
  have s5 := row! s4,12,60,2567371549187,17625858035239
  have s6 := row! s5,12,72,2160893720159,19786751755398
  have s7 := row! s6,12,84,1350468013462,21137219768860
  have s8 := row! s7,12,96,637083878646,21774303647506
  have s9 := row! s8,12,108,233020920150,22007324567656
  have s10 := row! s9,12,120,51521787574,22058846355230
  have s11 := row! s10,12,132,2953762622,22061800117852
  have s12 := row! s11,12,144,0,22061800117852
  have s13 := row! s12,8,152,0,22061800117852
  change P3_6_8_1.sumBelow _ 152 < layerNeed
  rw [s13]
  decide

private theorem m2_4 : availableMass (start .two) (⟨6,18,0⟩ : Shape) 72 < layerNeed := by
  rw [mass_eq (start .two) (⟨6,18,0⟩ : Shape) 72 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨6,18,0⟩ : Shape) 72) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,3000104969663,15058486486052
  have s5 := row! s4,12,60,2567371549187,17625858035239
  have s6 := row! s5,12,72,2177705640359,19803563675598
  have s7 := row! s6,12,84,1366145661992,21169709337590
  have s8 := row! s7,12,96,544805823848,21714515161438
  have s9 := row! s8,12,108,144231497384,21858746658822
  have s10 := row! s9,12,120,14092322792,21872838981614
  have s11 := row! s10,12,132,9979604,21872848961218
  have s12 := row! s11,8,140,0,21872848961218
  change P3_6_8_1.sumBelow _ 140 < layerNeed
  rw [s12]
  decide

private theorem m2_5 : availableMass (start .two) (⟨9,27,0⟩ : Shape) 76 < layerNeed := by
  rw [mass_eq (start .two) (⟨9,27,0⟩ : Shape) 76 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨9,27,0⟩ : Shape) 76) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,3000104969663,15058486486052
  have s5 := row! s4,12,60,2567371549187,17625858035239
  have s6 := row! s5,12,72,2177705640359,19803563675598
  have s7 := row! s6,12,84,1514008811021,21317572486619
  have s8 := row! s7,12,96,448588262474,21766160749093
  have s9 := row! s8,12,108,52613986238,21818774735331
  have s10 := row! s9,12,120,171062034,21818945797365
  have s11 := row! s10,6,126,0,21818945797365
  change P3_6_8_1.sumBelow _ 126 < layerNeed
  rw [s11]
  decide

private theorem m2_6 : availableMass (start .two) (⟨64,24,0⟩ : Shape) 82 < layerNeed := by
  rw [mass_eq (start .two) (⟨64,24,0⟩ : Shape) 82 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨64,24,0⟩ : Shape) 82) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,3000104969663,15058486486052
  have s5 := row! s4,12,60,2567371549187,17625858035239
  have s6 := row! s5,12,72,2177705640359,19803563675598
  have s7 := row! s6,12,84,1797432710077,21600996385675
  have s8 := row! s7,12,96,757035670687,22358032056362
  have s9 := row! s8,12,108,141118745011,22499150801373
  have s10 := row! s9,12,120,7511748775,22506662550148
  have s11 := row! s10,12,132,0,22506662550148
  have s12 := row! s11,5,137,0,22506662550148
  change P3_6_8_1.sumBelow _ 137 < layerNeed
  rw [s12]
  decide

private theorem m2_7 : availableMass (start .two) (⟨65,30,0⟩ : Shape) 84 < layerNeed := by
  rw [mass_eq (start .two) (⟨65,30,0⟩ : Shape) 84 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨65,30,0⟩ : Shape) 84) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,3000104969663,15058486486052
  have s5 := row! s4,12,60,2567371549187,17625858035239
  have s6 := row! s5,12,72,2177705640359,19803563675598
  have s7 := row! s6,12,84,1829003555243,21632567230841
  have s8 := row! s7,12,96,825765369582,22458332600423
  have s9 := row! s8,12,108,112947034638,22571279635061
  have s10 := row! s9,12,120,1962783060,22573242418121
  have s11 := row! s10,9,129,0,22573242418121
  change P3_6_8_1.sumBelow _ 129 < layerNeed
  rw [s11]
  decide

private theorem m2_8 : availableMass (start .two) (⟨93,37,0⟩ : Shape) 85 < layerNeed := by
  rw [mass_eq (start .two) (⟨93,37,0⟩ : Shape) 85 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨93,37,0⟩ : Shape) 85) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,3000104969663,15058486486052
  have s5 := row! s4,12,60,2567371549187,17625858035239
  have s6 := row! s5,12,72,2177705640359,19803563675598
  have s7 := row! s6,12,84,1829003555243,21632567230841
  have s8 := row! s7,12,96,813157988371,22445725219212
  have s9 := row! s8,12,108,63563716939,22509288936151
  have s10 := row! s9,12,120,71710263,22509360646414
  have s11 := row! s10,3,123,0,22509360646414
  change P3_6_8_1.sumBelow _ 123 < layerNeed
  rw [s11]
  decide

private theorem m2_9 : availableMass (start .two) (⟨93,40,0⟩ : Shape) 86 < layerNeed := by
  rw [mass_eq (start .two) (⟨93,40,0⟩ : Shape) 86 (Or.inr (by decide)) (by decide)]
  have s0 : P3_6_8_1.sumBelow (fastLayer (start .two) (⟨93,40,0⟩ : Shape) 86) 0 = 0 := rfl
  have s1 := row! s0,12,12,4577344072499,4577344072499
  have s2 := row! s1,12,24,4003054728023,8580398800522
  have s3 := row! s2,12,36,3477982715867,12058381516389
  have s4 := row! s3,12,48,3000104969663,15058486486052
  have s5 := row! s4,12,60,2567371549187,17625858035239
  have s6 := row! s5,12,72,2177705640359,19803563675598
  have s7 := row! s6,12,84,1829003555243,21632567230841
  have s8 := row! s7,12,96,889955890659,22522523121500
  have s9 := row! s8,12,108,64453079152,22586976200652
  have s10 := row! s9,12,120,24222825,22587000423477
  have s11 := row! s10,1,121,0,22587000423477
  change P3_6_8_1.sumBelow _ 121 < layerNeed
  rw [s11]
  decide

private theorem thresholds_valid (k : Band) (q : Threshold) (hq : q ∈ thresholds k) :
    0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  cases k
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m1_0⟩
    · exact ⟨by decide, m1_1⟩
    · exact ⟨by decide, m1_2⟩
    · exact ⟨by decide, m1_3⟩
    · exact ⟨by decide, m1_4⟩
    · exact ⟨by decide, m1_5⟩
    · exact ⟨by decide, m1_6⟩
    · exact ⟨by decide, m1_7⟩
    · exact ⟨by decide, m1_8⟩
    · exact ⟨by decide, m1_9⟩
    · exact ⟨by decide, m1_10⟩
    · exact ⟨by decide, m1_11⟩
    · exact ⟨by decide, m1_12⟩
    · exact ⟨by decide, m1_13⟩
    · exact ⟨by decide, m1_14⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m2_0⟩
    · exact ⟨by decide, m2_1⟩
    · exact ⟨by decide, m2_2⟩
    · exact ⟨by decide, m2_3⟩
    · exact ⟨by decide, m2_4⟩
    · exact ⟨by decide, m2_5⟩
    · exact ⟨by decide, m2_6⟩
    · exact ⟨by decide, m2_7⟩
    · exact ⟨by decide, m2_8⟩
    · exact ⟨by decide, m2_9⟩

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
end Low48PriceMass
