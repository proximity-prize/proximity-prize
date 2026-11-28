import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0619
import ProximityPrize.SubmissionLower.Z6969Pack0620
import ProximityPrize.SubmissionLower.Z6969Pack0621
import ProximityPrize.SubmissionLower.Z6969Pack0622

section Pack_R6970Height2313CommonRanks74

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks74_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_11577_2548 :
    P1_7_1.groupedPoleMoment 11577 2548 ≤ 498847383098023 :=
  _root_.Research6969.PackedRanks.PackedRanks363To365.moment11577_2548

private theorem pole_11577_2564 :
    P1_7_1.groupedPoleMoment 11577 2564 ≤ 501284470461675 :=
  _root_.PoleAffine6970.certified 11577 2564 501284470461675 (by decide) (by decide +kernel)

private theorem pole_11577_2615 :
    P1_7_1.groupedPoleMoment 11577 2615 ≤ 509018341309343 :=
  _root_.Research6969.PackedRanks.PackedRanks366To368.moment11577_2615

private theorem pole_11579_2548 :
    P1_7_1.groupedPoleMoment 11579 2548 ≤ 499124969898998 :=
  _root_.Research6969.PackedRanks.PackedRanks366To368.moment11579_2548

private theorem pole_11579_2552 :
    P1_7_1.groupedPoleMoment 11579 2552 ≤ 499735082985067 :=
  _root_.PoleAffine6970.certified 11579 2552 499735082985067 (by decide) (by decide +kernel)

private theorem pole_11579_2556 :
    P1_7_1.groupedPoleMoment 11579 2556 ≤ 500344869187388 :=
  _root_.PoleAffine6970.certified 11579 2556 500344869187388 (by decide) (by decide +kernel)

private theorem pole_11579_2615 :
    P1_7_1.groupedPoleMoment 11579 2615 ≤ 509301798386539 :=
  _root_.Research6969.PackedRanks.PackedRanks369To371.moment11579_2615

private theorem pole_11580_2548 :
    P1_7_1.groupedPoleMoment 11580 2548 ≤ 499263802703202 :=
  _root_.Research6969.PackedRanks.PackedRanks369To371.moment11580_2548

private theorem pole_11581_2548 :
    P1_7_1.groupedPoleMoment 11581 2548 ≤ 499402661779949 :=
  _root_.Research6969.PackedRanks.PackedRanks372To374.moment11581_2548

private theorem pole_11582_2547 :
    P1_7_1.groupedPoleMoment 11582 2547 ≤ 499388835538415 :=
  _root_.PoleAffine6970.certified 11582 2547 499388835538415 (by decide) (by decide +kernel)

theorem bank_8330_11577_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8330,11577,2548,u⟩,17540864495845376,498847383098023⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8330 11577 2548 u 17540864495845376 498847383098023
    (by decide) (by decide) (by decide) (by decide) pole_11577_2548

theorem bank_8301_11577_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8301,11577,2548,u⟩,17404404995719168,498847383098023⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8301 11577 2548 u 17404404995719168 498847383098023
    (by decide) (by decide) (by decide) (by decide) pole_11577_2548

theorem bank_8338_11577_2564 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8338,11577,2564,u⟩,17662430167695360,501284470461675⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8338 11577 2564 u 17662430167695360 501284470461675
    (by decide) (by decide) (by decide) (by decide) pole_11577_2564

theorem bank_8348_11577_2615 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8348,11577,2615,u⟩,17976439182721024,509018341309343⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8348 11577 2615 u 17976439182721024 509018341309343
    (by decide) (by decide) (by decide) (by decide) pole_11577_2615

theorem bank_8333_11579_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8333,11579,2548,u⟩,17555013069701120,499124969898998⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8333 11579 2548 u 17555013069701120 499124969898998
    (by decide) (by decide) (by decide) (by decide) pole_11579_2548

theorem bank_8340_11579_2552 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8340,11579,2552,u⟩,17609037937377280,499735082985067⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8340 11579 2552 u 17609037937377280 499735082985067
    (by decide) (by decide) (by decide) (by decide) pole_11579_2552

theorem bank_8339_11579_2556 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8339,11579,2556,u⟩,17625278836113408,500344869187388⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8339 11579 2556 u 17625278836113408 500344869187388
    (by decide) (by decide) (by decide) (by decide) pole_11579_2556

theorem bank_8341_11579_2615 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8341,11579,2615,u⟩,17942656501940224,509301798386539⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8341 11579 2615 u 17942656501940224 509301798386539
    (by decide) (by decide) (by decide) (by decide) pole_11579_2615

theorem bank_8301_11580_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8301,11580,2548,u⟩,17404404995719168,499263802703202⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8301 11580 2548 u 17404404995719168 499263802703202
    (by decide) (by decide) (by decide) (by decide) pole_11580_2548

theorem bank_8332_11580_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8332,11580,2548,u⟩,17550296210210816,499263802703202⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8332 11580 2548 u 17550296210210816 499263802703202
    (by decide) (by decide) (by decide) (by decide) pole_11580_2548

theorem bank_8308_11581_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8308,11581,2548,u⟩,17437292043960320,499402661779949⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8308 11581 2548 u 17437292043960320 499402661779949
    (by decide) (by decide) (by decide) (by decide) pole_11581_2548

theorem bank_8337_11581_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8337,11581,2548,u⟩,17573887189712896,499402661779949⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8337 11581 2548 u 17573887189712896 499402661779949
    (by decide) (by decide) (by decide) (by decide) pole_11581_2548

theorem bank_8315_11582_2547 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8315,11582,2547,u⟩,17465000554659840,499388835538415⟩ :=
  pack_R6970Height2313CommonRanks74_bank_checked 8315 11582 2547 u 17465000554659840 499388835538415
    (by decide) (by decide) (by decide) (by decide) pole_11582_2547

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks74

section Pack_R6970Height2313CommonRanks75

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks75_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_11582_2548 :
    P1_7_1.groupedPoleMoment 11582 2548 ≤ 499541547131788 :=
  _root_.Research6969.PackedRanks.PackedRanks372To374.moment11582_2548

private theorem pole_11611_2580 :
    P1_7_1.groupedPoleMoment 11611 2580 ≤ 508497594730893 :=
  _root_.PoleAffine6970.certified 11611 2580 508497594730893 (by decide) (by decide +kernel)

private theorem pole_11639_2548 :
    P1_7_1.groupedPoleMoment 11639 2548 ≤ 507501527779128 :=
  _root_.PoleAffine6970.certified 11639 2548 507501527779128 (by decide) (by decide +kernel)

private theorem pole_11810_2547 :
    P1_7_1.groupedPoleMoment 11810 2547 ≤ 531735451845147 :=
  _root_.PoleAffine6970.certified 11810 2547 531735451845147 (by decide) (by decide +kernel)

private theorem pole_11810_2598 :
    P1_7_1.groupedPoleMoment 11810 2598 ≤ 540020413005418 :=
  _root_.PoleAffine6970.certified 11810 2598 540020413005418 (by decide) (by decide +kernel)

private theorem pole_12147_2622 :
    P1_7_1.groupedPoleMoment 12147 2622 ≤ 595475399274745 :=
  _root_.PoleAffine6970.certified 12147 2622 595475399274745 (by decide) (by decide +kernel)

private theorem pole_12157_2622 :
    P1_7_1.groupedPoleMoment 12157 2622 ≤ 597054651075325 :=
  _root_.PoleAffine6970.certified 12157 2622 597054651075325 (by decide) (by decide +kernel)

private theorem pole_12159_2675 :
    P1_7_1.groupedPoleMoment 12159 2675 ≤ 606766727288477 :=
  _root_.PoleAffine6970.certified 12159 2675 606766727288477 (by decide) (by decide +kernel)

private theorem pole_12160_2622 :
    P1_7_1.groupedPoleMoment 12160 2622 ≤ 597528981303932 :=
  _root_.PoleAffine6970.certified 12160 2622 597528981303932 (by decide) (by decide +kernel)

private theorem pole_13884_3070 :
    P1_7_1.groupedPoleMoment 13884 3070 ≤ 1035530902486423 :=
  _root_.PoleAffine6970.certified 13884 3070 1035530902486423 (by decide) (by decide +kernel)

theorem bank_8312_11582_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8312,11582,2548,u⟩,17456099343466496,499541547131788⟩ :=
  pack_R6970Height2313CommonRanks75_bank_checked 8312 11582 2548 u 17456099343466496 499541547131788
    (by decide) (by decide) (by decide) (by decide) pole_11582_2548

theorem bank_8366_11611_2580 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8366,11611,2580,u⟩,17879833989873664,508497594730893⟩ :=
  pack_R6970Height2313CommonRanks75_bank_checked 8366 11611 2580 u 17879833989873664 508497594730893
    (by decide) (by decide) (by decide) (by decide) pole_11611_2580

theorem bank_8372_11639_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8372,11639,2548,u⟩,17739491789766656,507501527779128⟩ :=
  pack_R6970Height2313CommonRanks75_bank_checked 8372 11639 2548 u 17739491789766656 507501527779128
    (by decide) (by decide) (by decide) (by decide) pole_11639_2548

theorem bank_8473_11810_2547 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8473,11810,2547,u⟩,18216515147923456,531735451845147⟩ :=
  pack_R6970Height2313CommonRanks75_bank_checked 8473 11810 2547 u 18216515147923456 531735451845147
    (by decide) (by decide) (by decide) (by decide) pole_11810_2547

theorem bank_8505_11810_2598 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8505,11810,2598,u⟩,18650290068914176,540020413005418⟩ :=
  pack_R6970Height2313CommonRanks75_bank_checked 8505 11810 2598 u 18650290068914176 540020413005418
    (by decide) (by decide) (by decide) (by decide) pole_11810_2598

theorem bank_8710_12147_2622 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8710,12147,2622,u⟩,19809629157457920,595475399274745⟩ :=
  pack_R6970Height2313CommonRanks75_bank_checked 8710 12147 2622 u 19809629157457920 595475399274745
    (by decide) (by decide) (by decide) (by decide) pole_12147_2622

theorem bank_8714_12157_2622 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8714,12157,2622,u⟩,19829986352955392,597054651075325⟩ :=
  pack_R6970Height2313CommonRanks75_bank_checked 8714 12157 2622 u 19829986352955392 597054651075325
    (by decide) (by decide) (by decide) (by decide) pole_12157_2622

theorem bank_8714_12159_2675 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8714,12159,2675,u⟩,20134330585579520,606766727288477⟩ :=
  pack_R6970Height2313CommonRanks75_bank_checked 8714 12159 2675 u 20134330585579520 606766727288477
    (by decide) (by decide) (by decide) (by decide) pole_12159_2675

theorem bank_8714_12160_2622 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8714,12160,2622,u⟩,19829986352955392,597528981303932⟩ :=
  pack_R6970Height2313CommonRanks75_bank_checked 8714 12160 2622 u 19829986352955392 597528981303932
    (by decide) (by decide) (by decide) (by decide) pole_12160_2622

theorem bank_10000_13884_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10000,13884,3070,u⟩,30428373265940480,1035530902486423⟩ :=
  pack_R6970Height2313CommonRanks75_bank_checked 10000 13884 3070 u 30428373265940480 1035530902486423
    (by decide) (by decide) (by decide) (by decide) pole_13884_3070

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks75
