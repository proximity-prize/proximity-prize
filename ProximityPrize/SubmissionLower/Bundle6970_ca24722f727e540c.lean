import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0634
import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound

section Pack_R6970Height2308SeedTwoPrimaryFree00

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedTwoPrimary.BankRank00

private theorem pack_R6970Height2308SeedTwoPrimaryFree00_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_144_32 :
    P1_7_1.groupedPoleMoment 144 32 ≤ 12729182 :=
  (_root_.Research6969.TransitionBanks.rank1 0).moment.1

private theorem pole_158_35 :
    P1_7_1.groupedPoleMoment 158 35 ≤ 18313194 :=
  (_root_.Research6969.TransitionBanks.rank8 0).moment.1

private theorem pole_172_38 :
    P1_7_1.groupedPoleMoment 172 38 ≤ 25559185 :=
  (_root_.Research6969.TransitionBanks.rank14 0).moment.1

theorem bank_104_144_32 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨104,144,32,u⟩,35837181952,12729182⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree00_bank_checked 104 144 32 u 35837181952 12729182
    (by decide) (by decide) (by decide) (by decide) pole_144_32

theorem bank_114_158_35 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨114,158,35,u⟩,46942126080,18313194⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree00_bank_checked 114 158 35 u 46942126080 18313194
    (by decide) (by decide) (by decide) (by decide) pole_158_35

theorem bank_124_172_38 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨124,172,38,u⟩,60131901440,25559185⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree00_bank_checked 124 172 38 u 60131901440 25559185
    (by decide) (by decide) (by decide) (by decide) pole_172_38

end Research6970.Height2308.SeedTwoPrimary.BankRank00
namespace Research6970.Height2308.SeedTwoPrimary
open Research6969

abbrev bank0 : P1_7.Bank := ⟨⟨104,144,32,1555⟩,35837181952,12729182⟩
theorem free0 : TransitionSources.Free 2308 0 bank0 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 0 bank0) 2308 = 15728054224 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 0 bank0) 2309 = 386838659984 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank00.bank_104_144_32 1555, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank1 : P1_7.Bank := ⟨⟨114,158,35,1693⟩,46942126080,18313194⟩
theorem free1 : TransitionSources.Free 2308 1 bank1 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 1 bank1) 2308 = 59501285844 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 1 bank1) 2309 = 621780951792 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank00.bank_114_158_35 1693, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank2 : P1_7.Bank := ⟨⟨124,172,38,1832⟩,60131901440,25559185⟩
theorem free2 : TransitionSources.Free 2308 2 bank2 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 2 bank2) 2308 = 6550373973 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 2 bank2) 2309 = 832414156782 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank00.bank_124_172_38 1832, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedTwoPrimary
end Pack_R6970Height2308SeedTwoPrimaryFree00

section Pack_R6970Height2308SeedTwoPrimaryFree01

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedTwoPrimary.BankRank01

private theorem pack_R6970Height2308SeedTwoPrimaryFree01_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_190_42 :
    P1_7_1.groupedPoleMoment 190 42 ≤ 37902732 :=
  _root_.PoleAffine6970.certified 190 42 37902732 (by decide) (by decide +kernel)

private theorem pole_215_47 :
    P1_7_1.groupedPoleMoment 215 47 ≤ 61311840 :=
  (_root_.Research6969.TransitionBanks.rank32 0).moment.1

private theorem pole_266_59 :
    P1_7_1.groupedPoleMoment 266 59 ≤ 144192301 :=
  _root_.PoleAffine6970.certified 266 59 144192301 (by decide) (by decide +kernel)

theorem bank_137_190_42 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨137,190,42,u⟩,80832888832,37902732⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree01_bank_checked 137 190 42 u 80832888832 37902732
    (by decide) (by decide) (by decide) (by decide) pole_190_42

theorem bank_155_215_47 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨155,215,47,u⟩,115657932800,61311840⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree01_bank_checked 155 215 47 u 115657932800 61311840
    (by decide) (by decide) (by decide) (by decide) pole_215_47

theorem bank_192_266_59 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨192,266,59,u⟩,220738355200,144192301⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree01_bank_checked 192 266 59 u 220738355200 144192301
    (by decide) (by decide) (by decide) (by decide) pole_266_59

end Research6970.Height2308.SeedTwoPrimary.BankRank01
namespace Research6970.Height2308.SeedTwoPrimary
open Research6969

abbrev bank3 : P1_7.Bank := ⟨⟨137,190,42,1901⟩,80832888832,37902732⟩
theorem free3 : TransitionSources.Free 2308 3 bank3 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 3 bank3) 2308 = 36387388338 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 3 bank3) 2309 = 1202528099412 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank01.bank_137_190_42 1901, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank4 : P1_7.Bank := ⟨⟨155,215,47,2251⟩,115657932800,61311840⟩
theorem free4 : TransitionSources.Free 2308 5 bank4 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 5 bank4) 2308 = 211025470608 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 5 bank4) 2309 = 2484094317840 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank01.bank_155_215_47 2251, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank5 : P1_7.Bank := ⟨⟨192,266,59,2846⟩,220738355200,144192301⟩
theorem free5 : TransitionSources.Free 2308 9 bank5 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 9 bank5) 2308 = 46968735528 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 9 bank5) 2309 = 6685290045954 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank01.bank_192_266_59 2846, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedTwoPrimary
end Pack_R6970Height2308SeedTwoPrimaryFree01

section Pack_R6970Height2308SeedTwoPrimaryFree02

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedTwoPrimary.BankRank02

private theorem pack_R6970Height2308SeedTwoPrimaryFree02_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_285_64 :
    P1_7_1.groupedPoleMoment 285 64 ≤ 191426557 :=
  _root_.PoleAffine6970.certified 285 64 191426557 (by decide) (by decide +kernel)

private theorem pole_297_66 :
    P1_7_1.groupedPoleMoment 297 66 ≤ 223698864 :=
  _root_.PoleAffine6970.certified 297 66 223698864 (by decide) (by decide +kernel)

private theorem pole_351_78 :
    P1_7_1.groupedPoleMoment 351 78 ≤ 434522864 :=
  _root_.PoleAffine6970.certified 351 78 434522864 (by decide) (by decide +kernel)

theorem bank_206_285_64 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨206,285,64,u⟩,274418892800,191426557⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree02_bank_checked 206 285 64 u 274418892800 191426557
    (by decide) (by decide) (by decide) (by decide) pole_285_64

theorem bank_214_297_66 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨214,297,66,u⟩,305712857088,223698864⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree02_bank_checked 214 297 66 u 305712857088 223698864
    (by decide) (by decide) (by decide) (by decide) pole_297_66

theorem bank_253_351_78 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨253,351,78,u⟩,503341383680,434522864⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree02_bank_checked 253 351 78 u 503341383680 434522864
    (by decide) (by decide) (by decide) (by decide) pole_351_78

end Research6970.Height2308.SeedTwoPrimary.BankRank02
namespace Research6970.Height2308.SeedTwoPrimary
open Research6969

abbrev bank6 : P1_7.Bank := ⟨⟨206,285,64,3831⟩,274418892800,191426557⟩
theorem free6 : TransitionSources.Free 2308 12 bank6 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 12 bank6) 2308 = 486984414596 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 12 bank6) 2309 = 15243987458088 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank02.bank_206_285_64 3831, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank7 : P1_7.Bank := ⟨⟨214,297,66,2459⟩,305712857088,223698864⟩
theorem free7 : TransitionSources.Free 2308 9 bank7 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 9 bank7) 2308 = 138922427490 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 9 bank7) 2309 = 6900901252290 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank02.bank_214_297_66 2459, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank8 : P1_7.Bank := ⟨⟨253,351,78,2768⟩,503341383680,434522864⟩
theorem free8 : TransitionSources.Free 2308 12 bank8 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 12 bank8) 2308 = 19842421404 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 12 bank8) 2309 = 13750553101077 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank02.bank_253_351_78 2768, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedTwoPrimary
end Pack_R6970Height2308SeedTwoPrimaryFree02

section Pack_R6970Height2308SeedTwoPrimaryFree03

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedTwoPrimary.BankRank03

private theorem pack_R6970Height2308SeedTwoPrimaryFree03_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_377_83 :
    P1_7_1.groupedPoleMoment 377 83 ≤ 573233613 :=
  _root_.PoleAffine6970.certified 377 83 573233613 (by decide) (by decide +kernel)

private theorem pole_383_86 :
    P1_7_1.groupedPoleMoment 383 86 ≤ 619714957 :=
  _root_.PoleAffine6970.certified 383 86 619714957 (by decide) (by decide +kernel)

private theorem pole_430_97 :
    P1_7_1.groupedPoleMoment 430 97 ≤ 985806433 :=
  _root_.PoleAffine6970.certified 430 97 985806433 (by decide) (by decide +kernel)

theorem bank_272_377_83 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨272,377,83,u⟩,619869372416,573233613⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree03_bank_checked 272 377 83 u 619869372416 573233613
    (by decide) (by decide) (by decide) (by decide) pole_377_83

theorem bank_310_430_97 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨310,430,97,u⟩,933129093120,985806433⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree03_bank_checked 310 430 97 u 933129093120 985806433
    (by decide) (by decide) (by decide) (by decide) pole_430_97

theorem bank_276_383_86 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨276,383,86,u⟩,657687052288,619714957⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree03_bank_checked 276 383 86 u 657687052288 619714957
    (by decide) (by decide) (by decide) (by decide) pole_383_86

end Research6970.Height2308.SeedTwoPrimary.BankRank03
namespace Research6970.Height2308.SeedTwoPrimary
open Research6969

abbrev bank9 : P1_7.Bank := ⟨⟨272,377,83,5630⟩,619869372416,573233613⟩
theorem free9 : TransitionSources.Free 2308 20 bank9 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 20 bank9) 2308 = 2257228559976 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 20 bank9) 2309 = 71269640736258 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank03.bank_272_377_83 5630, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank10 : P1_7.Bank := ⟨⟨310,430,97,3142⟩,933129093120,985806433⟩
theorem free10 : TransitionSources.Free 2308 16 bank10 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 16 bank10) 2308 = 2941699977272 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 16 bank10) 2309 = 34935070224418 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank03.bank_310_430_97 3142, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank11 : P1_7.Bank := ⟨⟨276,383,86,8410⟩,657687052288,619714957⟩
theorem free11 : TransitionSources.Free 2308 23 bank11 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 23 bank11) 2308 = 2757846420836 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 23 bank11) 2309 = 166632242846212 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank03.bank_276_383_86 8410, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedTwoPrimary
end Pack_R6970Height2308SeedTwoPrimaryFree03

section Pack_R6970Height2308SeedTwoPrimaryFree04

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedTwoPrimary.BankRank04

private theorem pack_R6970Height2308SeedTwoPrimaryFree04_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_538_121 :
    P1_7_1.groupedPoleMoment 538 121 ≤ 2400933278 :=
  _root_.PoleAffine6970.certified 538 121 2400933278 (by decide) (by decide +kernel)

private theorem pole_553_124 :
    P1_7_1.groupedPoleMoment 553 124 ≤ 2672787483 :=
  _root_.PoleAffine6970.certified 553 124 2672787483 (by decide) (by decide +kernel)

private theorem pole_724_162 :
    P1_7_1.groupedPoleMoment 724 162 ≤ 7812267014 :=
  _root_.PoleAffine6970.certified 724 162 7812267014 (by decide) (by decide +kernel)

theorem bank_388_538_121 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨388,538,121,u⟩,1819511357440,2400933278⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree04_bank_checked 388 538 121 u 1819511357440 2400933278
    (by decide) (by decide) (by decide) (by decide) pole_538_121

theorem bank_522_724_162 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨522,724,162,u⟩,4400964698112,7812267014⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree04_bank_checked 522 724 162 u 4400964698112 7812267014
    (by decide) (by decide) (by decide) (by decide) pole_724_162

theorem bank_399_553_124 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨399,553,124,u⟩,1972895744000,2672787483⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree04_bank_checked 399 553 124 u 1972895744000 2672787483
    (by decide) (by decide) (by decide) (by decide) pole_553_124

end Research6970.Height2308.SeedTwoPrimary.BankRank04
namespace Research6970.Height2308.SeedTwoPrimary
open Research6969

abbrev bank12 : P1_7.Bank := ⟨⟨388,538,121,3628⟩,1819511357440,2400933278⟩
theorem free12 : TransitionSources.Free 2308 21 bank12 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 21 bank12) 2308 = 6720654521608 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 21 bank12) 2309 = 87711048058664 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank04.bank_388_538_121 3628, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank13 : P1_7.Bank := ⟨⟨522,724,162,5849⟩,4400964698112,7812267014⟩
theorem free13 : TransitionSources.Free 2308 37 bank13 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 37 bank13) 2308 = 31544612567325 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 37 bank13) 2309 = 527206254658200 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank04.bank_522_724_162 5849, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank14 : P1_7.Bank := ⟨⟨399,553,124,9484⟩,1972895744000,2672787483⟩
theorem free14 : TransitionSources.Free 2308 36 bank14 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 36 bank14) 2308 = 12259351563795 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 36 bank14) 2309 = 609458836301910 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank04.bank_399_553_124 9484, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedTwoPrimary
end Pack_R6970Height2308SeedTwoPrimaryFree04

section Pack_R6970Height2308SeedTwoPrimaryFree05

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedTwoPrimary.BankRank05

private theorem pack_R6970Height2308SeedTwoPrimaryFree05_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_775_172 :
    P1_7_1.groupedPoleMoment 775 172 ≤ 10184948042 :=
  _root_.PoleAffine6970.certified 775 172 10184948042 (by decide) (by decide +kernel)

private theorem pole_1148_256 :
    P1_7_1.groupedPoleMoment 1148 256 ≤ 49047024630 :=
  _root_.PoleAffine6970.certified 1148 256 49047024630 (by decide) (by decide +kernel)

private theorem pole_1251_281 :
    P1_7_1.groupedPoleMoment 1251 281 ≤ 69511525887 :=
  _root_.PoleAffine6970.certified 1251 281 69511525887 (by decide) (by decide +kernel)

theorem bank_559_775_172 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨559,775,172,u⟩,5366645522432,10184948042⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree05_bank_checked 559 775 172 u 5366645522432 10184948042
    (by decide) (by decide) (by decide) (by decide) pole_775_172

theorem bank_902_1251_281 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨902,1251,281,u⟩,22686661345280,69511525887⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree05_bank_checked 902 1251 281 u 22686661345280 69511525887
    (by decide) (by decide) (by decide) (by decide) pole_1251_281

theorem bank_828_1148_256 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨828,1148,256,u⟩,17456501882880,49047024630⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree05_bank_checked 828 1148 256 u 17456501882880 49047024630
    (by decide) (by decide) (by decide) (by decide) pole_1148_256

end Research6970.Height2308.SeedTwoPrimary.BankRank05
namespace Research6970.Height2308.SeedTwoPrimary
open Research6969

abbrev bank15 : P1_7.Bank := ⟨⟨559,775,172,49578⟩,5366645522432,10184948042⟩
theorem free15 : TransitionSources.Free 2308 64 bank15 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 64 bank15) 2308 = 4316441345152 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 64 bank15) 2309 = 43110023308533056 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank05.bank_559_775_172 49578, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank16 : P1_7.Bank := ⟨⟨902,1251,281,11420⟩,22686661345280,69511525887⟩
theorem free16 : TransitionSources.Free 2308 77 bank16 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 77 bank16) 2308 = 81296241957477 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 77 bank16) 2309 = 9508334118475473 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank05.bank_902_1251_281 11420, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank17 : P1_7.Bank := ⟨⟨828,1148,256,167139⟩,17456501882880,49047024630⟩
theorem free17 : TransitionSources.Free 2308 103 bank17 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 103 bank17) 2308 = 80510395831820 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 103 bank17) 2309 = 1557152687499884220 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank05.bank_828_1148_256 167139, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedTwoPrimary
end Pack_R6970Height2308SeedTwoPrimaryFree05

section Pack_R6970Height2308SeedTwoPrimaryFree06

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedTwoPrimary.BankRank06

private theorem pack_R6970Height2308SeedTwoPrimaryFree06_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_380_79 :
    P1_7_1.groupedPoleMoment 380 79 ≤ 566001366 :=
  _root_.PoleAffine6970.certified 380 79 566001366 (by decide) (by decide +kernel)

private theorem pole_380_80 :
    P1_7_1.groupedPoleMoment 380 80 ≤ 571535615 :=
  _root_.PoleAffine6970.certified 380 80 571535615 (by decide) (by decide +kernel)

private theorem pole_388_83 :
    P1_7_1.groupedPoleMoment 388 83 ≤ 628633573 :=
  _root_.PoleAffine6970.certified 388 83 628633573 (by decide) (by decide +kernel)

theorem bank_273_380_79 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨273,380,79,u⟩,602113310720,566001366⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree06_bank_checked 273 380 79 u 602113310720 566001366
    (by decide) (by decide) (by decide) (by decide) pole_380_79

theorem bank_279_388_83 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨279,388,83,u⟩,656015360000,628633573⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree06_bank_checked 279 388 83 u 656015360000 628633573
    (by decide) (by decide) (by decide) (by decide) pole_388_83

theorem bank_273_380_80 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨273,380,80,u⟩,607870255104,571535615⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree06_bank_checked 273 380 80 u 607870255104 571535615
    (by decide) (by decide) (by decide) (by decide) pole_380_80

end Research6970.Height2308.SeedTwoPrimary.BankRank06
namespace Research6970.Height2308.SeedTwoPrimary
open Research6969

abbrev bank18 : P1_7.Bank := ⟨⟨273,380,79,46272⟩,602113310720,566001366⟩
theorem free18 : TransitionSources.Free 2308 25 bank18 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 25 bank18) 2308 = 1761660493552 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 25 bank18) 2309 = 4599119038354756 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank06.bank_273_380_79 46272, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank19 : P1_7.Bank := ⟨⟨279,388,83,62695⟩,656015360000,628633573⟩
theorem free19 : TransitionSources.Free 2308 27 bank19 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 27 bank19) 2308 = 2127398916512 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 27 bank19) 2309 = 9097122103116496 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank06.bank_279_388_83 62695, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank20 : P1_7.Bank := ⟨⟨273,380,80,29985⟩,607870255104,571535615⟩
theorem free20 : TransitionSources.Free 2308 25 bank20 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 25 bank20) 2308 = 597119494136 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 25 bank20) 2309 = 1943289511638376 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank06.bank_273_380_80 29985, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedTwoPrimary
end Pack_R6970Height2308SeedTwoPrimaryFree06

section Pack_R6970Height2308SeedTwoPrimaryFree07

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedTwoPrimary.BankRank07

private theorem pack_R6970Height2308SeedTwoPrimaryFree07_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_1781_395 :
    P1_7_1.groupedPoleMoment 1781 395 ≤ 282195384964 :=
  _root_.PoleAffine6970.certified 1781 395 282195384964 (by decide) (by decide +kernel)

theorem bank_1283_1781_395 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1283,1781,395,u⟩,64607380045824,282195384964⟩ :=
  pack_R6970Height2308SeedTwoPrimaryFree07_bank_checked 1283 1781 395 u 64607380045824 282195384964
    (by decide) (by decide) (by decide) (by decide) pole_1781_395

end Research6970.Height2308.SeedTwoPrimary.BankRank07
namespace Research6970.Height2308.SeedTwoPrimary
open Research6969

abbrev bank21 : P1_7.Bank := ⟨⟨1283,1781,395,16994⟩,64607380045824,282195384964⟩
theorem free21 : TransitionSources.Free 2308 116 bank21 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 116 bank21) 2308 = 451583357037780 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 116 bank21) 2309 = 59108269213064940 := by decide +kernel
  refine ⟨Research6970.Height2308.SeedTwoPrimary.BankRank07.bank_1283_1781_395 16994, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedTwoPrimary
end Pack_R6970Height2308SeedTwoPrimaryFree07
