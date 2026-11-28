import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0643
import ProximityPrize.SubmissionLower.Z6969Pack0644

section Pack_R6970Height2313CommonRanks30

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks30_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3203_702 :
    P1_7_1.groupedPoleMoment 3203 702 ≤ 2918855628076 :=
  _root_.Research6969.PackedRanks.TerminalRanks24To27.moment3203_702

private theorem pole_3203_706 :
    P1_7_1.groupedPoleMoment 3203 706 ≤ 2931788577831 :=
  _root_.PoleAffine6970.certified 3203 706 2931788577831 (by decide) (by decide +kernel)

private theorem pole_3203_724 :
    P1_7_1.groupedPoleMoment 3203 724 ≤ 2989680899568 :=
  _root_.Research6969.PackedRanks.TerminalRanks24To27.moment3203_724

private theorem pole_3204_702 :
    P1_7_1.groupedPoleMoment 3204 702 ≤ 2921790084349 :=
  _root_.Research6969.PackedRanks.TerminalRanks24To27.moment3204_702

private theorem pole_3204_706 :
    P1_7_1.groupedPoleMoment 3204 706 ≤ 2934736528158 :=
  _root_.PoleAffine6970.certified 3204 706 2934736528158 (by decide) (by decide +kernel)

private theorem pole_3204_724 :
    P1_7_1.groupedPoleMoment 3204 724 ≤ 2992689220368 :=
  _root_.Research6969.PackedRanks.TerminalRanks24To27.moment3204_724

private theorem pole_3205_702 :
    P1_7_1.groupedPoleMoment 3205 702 ≤ 2924726546984 :=
  _root_.PoleAffine6970.certified 3205 702 2924726546984 (by decide) (by decide +kernel)

private theorem pole_3205_722 :
    P1_7_1.groupedPoleMoment 3205 722 ≤ 2989278090495 :=
  _root_.PoleAffine6970.certified 3205 722 2989278090495 (by decide) (by decide +kernel)

private theorem pole_3206_702 :
    P1_7_1.groupedPoleMoment 3206 702 ≤ 2927665016684 :=
  _root_.Research6969.PackedRanks.TerminalRanks28To31.moment3206_702

private theorem pole_3206_710 :
    P1_7_1.groupedPoleMoment 3206 710 ≤ 2953586856669 :=
  _root_.PoleAffine6970.certified 3206 710 2953586856669 (by decide) (by decide +kernel)

theorem bank_2302_3203_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2302,3203,702,u⟩,369889537687552,2918855628076⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2302 3203 702 u 369889537687552 2918855628076
    (by decide) (by decide) (by decide) (by decide) pole_3203_702

theorem bank_2304_3203_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2304,3203,702,u⟩,370609179328512,2918855628076⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2304 3203 702 u 370609179328512 2918855628076
    (by decide) (by decide) (by decide) (by decide) pole_3203_702

theorem bank_2307_3203_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2307,3203,702,u⟩,371690023944192,2918855628076⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2307 3203 702 u 371690023944192 2918855628076
    (by decide) (by decide) (by decide) (by decide) pole_3203_702

theorem bank_2305_3203_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2305,3203,702,u⟩,370969276579840,2918855628076⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2305 3203 702 u 370969276579840 2918855628076
    (by decide) (by decide) (by decide) (by decide) pole_3203_702

theorem bank_2306_3203_706 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2306,3203,706,u⟩,372935678230528,2931788577831⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2306 3203 706 u 372935678230528 2931788577831
    (by decide) (by decide) (by decide) (by decide) pole_3203_706

theorem bank_2305_3203_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2305,3203,724,u⟩,379747886694400,2989680899568⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2305 3203 724 u 379747886694400 2989680899568
    (by decide) (by decide) (by decide) (by decide) pole_3203_724

theorem bank_2307_3204_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2307,3204,702,u⟩,371690023944192,2921790084349⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2307 3204 702 u 371690023944192 2921790084349
    (by decide) (by decide) (by decide) (by decide) pole_3204_702

theorem bank_2304_3204_706 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2304,3204,706,u⟩,372211941900288,2934736528158⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2304 3204 706 u 372211941900288 2934736528158
    (by decide) (by decide) (by decide) (by decide) pole_3204_706

theorem bank_2311_3204_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2311,3204,724,u⟩,381967532032000,2992689220368⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2311 3204 724 u 381967532032000 2992689220368
    (by decide) (by decide) (by decide) (by decide) pole_3204_724

theorem bank_2304_3204_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2304,3204,724,u⟩,379378610995200,2992689220368⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2304 3204 724 u 379378610995200 2992689220368
    (by decide) (by decide) (by decide) (by decide) pole_3204_724

theorem bank_2307_3205_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2307,3205,702,u⟩,371690023944192,2924726546984⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2307 3205 702 u 371690023944192 2924726546984
    (by decide) (by decide) (by decide) (by decide) pole_3205_702

theorem bank_2311_3205_722 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2311,3205,722,u⟩,381169062379520,2989278090495⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2311 3205 722 u 381169062379520 2989278090495
    (by decide) (by decide) (by decide) (by decide) pole_3205_722

theorem bank_2307_3206_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2307,3206,702,u⟩,371690023944192,2927665016684⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2307 3206 702 u 371690023944192 2927665016684
    (by decide) (by decide) (by decide) (by decide) pole_3206_702

theorem bank_2309_3206_710 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2309,3206,710,u⟩,375630078935040,2953586856669⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2309 3206 710 u 375630078935040 2953586856669
    (by decide) (by decide) (by decide) (by decide) pole_3206_710

theorem bank_2308_3206_710 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2308,3206,710,u⟩,375265883848704,2953586856669⟩ :=
  pack_R6970Height2313CommonRanks30_bank_checked 2308 3206 710 u 375265883848704 2953586856669
    (by decide) (by decide) (by decide) (by decide) pole_3206_710

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks30

section Pack_R6970Height2313CommonRanks32

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks32_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3209_722 :
    P1_7_1.groupedPoleMoment 3209 722 ≤ 3001313456975 :=
  _root_.PoleAffine6970.certified 3209 722 3001313456975 (by decide) (by decide +kernel)

private theorem pole_3209_724 :
    P1_7_1.groupedPoleMoment 3209 724 ≤ 3007761756493 :=
  _root_.Research6969.PackedRanks.TerminalRanks36To39.moment3209_724

private theorem pole_3213_724 :
    P1_7_1.groupedPoleMoment 3213 724 ≤ 3019856947443 :=
  _root_.PoleAffine6970.certified 3213 724 3019856947443 (by decide) (by decide +kernel)

private theorem pole_3214_724 :
    P1_7_1.groupedPoleMoment 3214 724 ≤ 3022885912618 :=
  _root_.PoleAffine6970.certified 3214 724 3022885912618 (by decide) (by decide +kernel)

private theorem pole_3218_724 :
    P1_7_1.groupedPoleMoment 3218 724 ≤ 3035022464818 :=
  _root_.PoleAffine6970.certified 3218 724 3035022464818 (by decide) (by decide +kernel)

private theorem pole_3224_718 :
    P1_7_1.groupedPoleMoment 3224 718 ≤ 3033622538054 :=
  _root_.PoleAffine6970.certified 3224 718 3033622538054 (by decide) (by decide +kernel)

private theorem pole_3271_716 :
    P1_7_1.groupedPoleMoment 3271 716 ≤ 3171444219448 :=
  _root_.PoleAffine6970.certified 3271 716 3171444219448 (by decide) (by decide +kernel)

private theorem pole_3273_719 :
    P1_7_1.groupedPoleMoment 3273 719 ≤ 3188049024550 :=
  _root_.PoleAffine6970.certified 3273 719 3188049024550 (by decide) (by decide +kernel)

private theorem pole_3273_737 :
    P1_7_1.groupedPoleMoment 3273 737 ≤ 3249894771545 :=
  _root_.PoleAffine6970.certified 3273 737 3249894771545 (by decide) (by decide +kernel)

private theorem pole_3369_737 :
    P1_7_1.groupedPoleMoment 3369 737 ≤ 3566970195593 :=
  _root_.PoleAffine6970.certified 3369 737 3566970195593 (by decide) (by decide +kernel)

theorem bank_2312_3209_722 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2312,3209,722,u⟩,381538835628032,3001313456975⟩ :=
  pack_R6970Height2313CommonRanks32_bank_checked 2312 3209 722 u 381538835628032 3001313456975
    (by decide) (by decide) (by decide) (by decide) pole_3209_722

theorem bank_2304_3209_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2304,3209,724,u⟩,379378610995200,3007761756493⟩ :=
  pack_R6970Height2313CommonRanks32_bank_checked 2304 3209 724 u 379378610995200 3007761756493
    (by decide) (by decide) (by decide) (by decide) pole_3209_724

theorem bank_2314_3209_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2314,3209,724,u⟩,383079920435200,3007761756493⟩ :=
  pack_R6970Height2313CommonRanks32_bank_checked 2314 3209 724 u 383079920435200 3007761756493
    (by decide) (by decide) (by decide) (by decide) pole_3209_724

theorem bank_2316_3213_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2316,3213,724,u⟩,383822462976000,3019856947443⟩ :=
  pack_R6970Height2313CommonRanks32_bank_checked 2316 3213 724 u 383822462976000 3019856947443
    (by decide) (by decide) (by decide) (by decide) pole_3213_724

theorem bank_2317_3214_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2317,3214,724,u⟩,384194019328000,3022885912618⟩ :=
  pack_R6970Height2313CommonRanks32_bank_checked 2317 3214 724 u 384194019328000 3022885912618
    (by decide) (by decide) (by decide) (by decide) pole_3214_724

theorem bank_2320_3218_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2320,3218,724,u⟩,385309828710400,3035022464818⟩ :=
  pack_R6970Height2313CommonRanks32_bank_checked 2320 3218 724 u 385309828710400 3035022464818
    (by decide) (by decide) (by decide) (by decide) pole_3218_724

theorem bank_2323_3224_718 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2323,3224,718,u⟩,383999087738880,3033622538054⟩ :=
  pack_R6970Height2313CommonRanks32_bank_checked 2323 3224 718 u 383999087738880 3033622538054
    (by decide) (by decide) (by decide) (by decide) pole_3224_718

theorem bank_2346_3271_716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2346,3271,716,u⟩,391734418997248,3171444219448⟩ :=
  pack_R6970Height2313CommonRanks32_bank_checked 2346 3271 716 u 391734418997248 3171444219448
    (by decide) (by decide) (by decide) (by decide) pole_3271_716

theorem bank_2347_3273_719 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2347,3273,719,u⟩,393355355750400,3188049024550⟩ :=
  pack_R6970Height2313CommonRanks32_bank_checked 2347 3273 719 u 393355355750400 3188049024550
    (by decide) (by decide) (by decide) (by decide) pole_3273_719

theorem bank_2348_3273_737 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2348,3273,737,u⟩,401176361435136,3249894771545⟩ :=
  pack_R6970Height2313CommonRanks32_bank_checked 2348 3273 737 u 401176361435136 3249894771545
    (by decide) (by decide) (by decide) (by decide) pole_3273_737

theorem bank_2415_3369_737 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2415,3369,737,u⟩,427275292508160,3566970195593⟩ :=
  pack_R6970Height2313CommonRanks32_bank_checked 2415 3369 737 u 427275292508160 3566970195593
    (by decide) (by decide) (by decide) (by decide) pole_3369_737

theorem bank_2425_3369_737 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2425,3369,737,u⟩,431245138329600,3566970195593⟩ :=
  pack_R6970Height2313CommonRanks32_bank_checked 2425 3369 737 u 431245138329600 3566970195593
    (by decide) (by decide) (by decide) (by decide) pole_3369_737

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks32
