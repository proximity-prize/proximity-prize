import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0634

section Pack_R6970Height2308SeedOnePrimaryFree00

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedOnePrimary

private theorem pack_R6970Height2308SeedOnePrimaryFree00_bank_checked (m b j u N P : ℕ)
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
  _root_.PoleAffine6970.certified 144 32 12729182 (by decide) (by decide +kernel)

private theorem pole_158_35 :
    P1_7_1.groupedPoleMoment 158 35 ≤ 18313194 :=
  _root_.PoleAffine6970.certified 158 35 18313194 (by decide) (by decide +kernel)

private theorem pole_172_38 :
    P1_7_1.groupedPoleMoment 172 38 ≤ 25559185 :=
  _root_.PoleAffine6970.certified 172 38 25559185 (by decide) (by decide +kernel)

theorem bank_104_144_32 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨104,144,32,u⟩,35837181952,12729182⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree00_bank_checked 104 144 32 u 35837181952 12729182
    (by decide) (by decide) (by decide) (by decide) pole_144_32

theorem bank_114_158_35 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨114,158,35,u⟩,46942126080,18313194⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree00_bank_checked 114 158 35 u 46942126080 18313194
    (by decide) (by decide) (by decide) (by decide) pole_158_35

theorem bank_124_172_38 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨124,172,38,u⟩,60131901440,25559185⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree00_bank_checked 124 172 38 u 60131901440 25559185
    (by decide) (by decide) (by decide) (by decide) pole_172_38

end Research6970.Height2308.SeedOnePrimary
namespace Research6970.Height2308.SeedOnePrimary
open Research6969

abbrev bank0 : P1_7.Bank := ⟨⟨104,144,32,1555⟩,35837181952,12729182⟩
theorem free0 : TransitionSources.Free 2308 0 bank0 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 0 bank0) 2308 = 15728054224 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 0 bank0) 2309 = 386838659984 := by decide +kernel
  refine ⟨bank_104_144_32 1555, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank1 : P1_7.Bank := ⟨⟨114,158,35,1693⟩,46942126080,18313194⟩
theorem free1 : TransitionSources.Free 2308 1 bank1 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 1 bank1) 2308 = 59501285844 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 1 bank1) 2309 = 621780951792 := by decide +kernel
  refine ⟨bank_114_158_35 1693, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank2 : P1_7.Bank := ⟨⟨124,172,38,1832⟩,60131901440,25559185⟩
theorem free2 : TransitionSources.Free 2308 2 bank2 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 2 bank2) 2308 = 6550373973 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 2 bank2) 2309 = 832414156782 := by decide +kernel
  refine ⟨bank_124_172_38 1832, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedOnePrimary
end Pack_R6970Height2308SeedOnePrimaryFree00

section Pack_R6970Height2308SeedOnePrimaryFree01

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedOnePrimary

private theorem pack_R6970Height2308SeedOnePrimaryFree01_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_186_41 :
    P1_7_1.groupedPoleMoment 186 41 ≤ 34768135 :=
  _root_.PoleAffine6970.certified 186 41 34768135 (by decide) (by decide +kernel)

private theorem pole_198_44 :
    P1_7_1.groupedPoleMoment 198 44 ≤ 44802338 :=
  _root_.PoleAffine6970.certified 198 44 44802338 (by decide) (by decide +kernel)

private theorem pole_215_47 :
    P1_7_1.groupedPoleMoment 215 47 ≤ 61311840 :=
  _root_.PoleAffine6970.certified 215 47 61311840 (by decide) (by decide +kernel)

theorem bank_134_186_41 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨134,186,41,u⟩,75585814528,34768135⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree01_bank_checked 134 186 41 u 75585814528 34768135
    (by decide) (by decide) (by decide) (by decide) pole_186_41

theorem bank_143_198_44 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨143,198,44,u⟩,92044001280,44802338⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree01_bank_checked 143 198 44 u 92044001280 44802338
    (by decide) (by decide) (by decide) (by decide) pole_198_44

theorem bank_155_215_47 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨155,215,47,u⟩,115657932800,61311840⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree01_bank_checked 155 215 47 u 115657932800 61311840
    (by decide) (by decide) (by decide) (by decide) pole_215_47

end Research6970.Height2308.SeedOnePrimary
namespace Research6970.Height2308.SeedOnePrimary
open Research6969

abbrev bank3 : P1_7.Bank := ⟨⟨134,186,41,1974⟩,75585814528,34768135⟩
theorem free3 : TransitionSources.Free 2308 3 bank3 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 3 bank3) 2308 = 134891599400 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 3 bank3) 2309 = 1318556345350 := by decide +kernel
  refine ⟨bank_134_186_41 1974, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank4 : P1_7.Bank := ⟨⟨143,198,44,2135⟩,92044001280,44802338⟩
theorem free4 : TransitionSources.Free 2308 4 bank4 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 4 bank4) 2308 = 172612540572 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 4 bank4) 2309 = 1826777551296 := by decide +kernel
  refine ⟨bank_143_198_44 2135, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank5 : P1_7.Bank := ⟨⟨155,215,47,2251⟩,115657932800,61311840⟩
theorem free5 : TransitionSources.Free 2308 5 bank5 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 5 bank5) 2308 = 211025470608 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 5 bank5) 2309 = 2484094317840 := by decide +kernel
  refine ⟨bank_155_215_47 2251, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedOnePrimary
end Pack_R6970Height2308SeedOnePrimaryFree01

section Pack_R6970Height2308SeedOnePrimaryFree02

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedOnePrimary

private theorem pack_R6970Height2308SeedOnePrimaryFree02_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_247_55 :
    P1_7_1.groupedPoleMoment 247 55 ≤ 107778015 :=
  _root_.PoleAffine6970.certified 247 55 107778015 (by decide) (by decide +kernel)

private theorem pole_285_64 :
    P1_7_1.groupedPoleMoment 285 64 ≤ 191426557 :=
  _root_.PoleAffine6970.certified 285 64 191426557 (by decide) (by decide +kernel)

private theorem pole_373_84 :
    P1_7_1.groupedPoleMoment 373 84 ≤ 559058208 :=
  _root_.PoleAffine6970.certified 373 84 559058208 (by decide) (by decide +kernel)

theorem bank_178_247_55 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨178,247,55,u⟩,176946151424,107778015⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree02_bank_checked 178 247 55 u 176946151424 107778015
    (by decide) (by decide) (by decide) (by decide) pole_247_55

theorem bank_206_285_64 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨206,285,64,u⟩,274418892800,191426557⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree02_bank_checked 206 285 64 u 274418892800 191426557
    (by decide) (by decide) (by decide) (by decide) pole_285_64

theorem bank_269_373_84 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨269,373,84,u⟩,610154577920,559058208⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree02_bank_checked 269 373 84 u 610154577920 559058208
    (by decide) (by decide) (by decide) (by decide) pole_373_84

end Research6970.Height2308.SeedOnePrimary
namespace Research6970.Height2308.SeedOnePrimary
open Research6969

abbrev bank6 : P1_7.Bank := ⟨⟨178,247,55,2421⟩,176946151424,107778015⟩
theorem free6 : TransitionSources.Free 2308 7 bank6 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 7 bank6) 2308 = 418250757428 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 7 bank6) 2309 = 4340323224496 := by decide +kernel
  refine ⟨bank_178_247_55 2421, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank7 : P1_7.Bank := ⟨⟨206,285,64,2879⟩,274418892800,191426557⟩
theorem free7 : TransitionSources.Free 2308 10 bank7 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 10 bank7) 2308 = 551699468640 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 10 bank7) 2309 = 8888047485120 := by decide +kernel
  refine ⟨bank_206_285_64 2879, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank8 : P1_7.Bank := ⟨⟨269,373,84,3612⟩,610154577920,559058208⟩
theorem free8 : TransitionSources.Free 2308 16 bank8 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 16 bank8) 2308 = 2230978063321 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 16 bank8) 2309 = 30358247226588 := by decide +kernel
  refine ⟨bank_269_373_84 3612, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedOnePrimary
end Pack_R6970Height2308SeedOnePrimaryFree02

section Pack_R6970Height2308SeedOnePrimaryFree03

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedOnePrimary

private theorem pack_R6970Height2308SeedOnePrimaryFree03_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_395_87 :
    P1_7_1.groupedPoleMoment 395 87 ≤ 690338549 :=
  _root_.PoleAffine6970.certified 395 87 690338549 (by decide) (by decide +kernel)

private theorem pole_517_117 :
    P1_7_1.groupedPoleMoment 517 117 ≤ 2058521540 :=
  _root_.PoleAffine6970.certified 517 117 2058521540 (by decide) (by decide +kernel)

private theorem pole_527_118 :
    P1_7_1.groupedPoleMoment 527 118 ≤ 2203657519 :=
  _root_.PoleAffine6970.certified 527 118 2203657519 (by decide) (by decide +kernel)

theorem bank_285_395_87 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨285,395,87,u⟩,712706621440,690338549⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree03_bank_checked 285 395 87 u 712706621440 690338549
    (by decide) (by decide) (by decide) (by decide) pole_395_87

theorem bank_373_517_117 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨373,517,117,u⟩,1624384208896,2058521540⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree03_bank_checked 373 517 117 u 1624384208896 2058521540
    (by decide) (by decide) (by decide) (by decide) pole_517_117

theorem bank_380_527_118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨380,527,118,u⟩,1704221474816,2203657519⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree03_bank_checked 380 527 118 u 1704221474816 2203657519
    (by decide) (by decide) (by decide) (by decide) pole_527_118

end Research6970.Height2308.SeedOnePrimary
namespace Research6970.Height2308.SeedOnePrimary
open Research6969

abbrev bank9 : P1_7.Bank := ⟨⟨285,395,87,5551⟩,712706621440,690338549⟩
theorem free9 : TransitionSources.Free 2308 21 bank9 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 21 bank9) 2308 = 2879924279200 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 21 bank9) 2309 = 79533675338816 := by decide +kernel
  refine ⟨bank_285_395_87 5551, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank10 : P1_7.Bank := ⟨⟨373,517,117,3694⟩,1624384208896,2058521540⟩
theorem free10 : TransitionSources.Free 2308 21 bank10 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 21 bank10) 2308 = 3580705461880 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 21 bank10) 2309 = 78887402337440 := by decide +kernel
  refine ⟨bank_373_517_117 3694, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank11 : P1_7.Bank := ⟨⟨380,527,118,7501⟩,1704221474816,2203657519⟩
theorem free11 : TransitionSources.Free 2308 32 bank11 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 32 bank11) 2308 = 2773706875478 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 32 bank11) 2309 = 327431455260679 := by decide +kernel
  refine ⟨bank_380_527_118 7501, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedOnePrimary
end Pack_R6970Height2308SeedOnePrimaryFree03

section Pack_R6970Height2308SeedOnePrimaryFree04

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedOnePrimary

private theorem pack_R6970Height2308SeedOnePrimaryFree04_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_642_142 :
    P1_7_1.groupedPoleMoment 642 142 ≤ 4794203956 :=
  _root_.PoleAffine6970.certified 642 142 4794203956 (by decide) (by decide +kernel)

private theorem pole_875_196 :
    P1_7_1.groupedPoleMoment 875 196 ≤ 16648066377 :=
  _root_.PoleAffine6970.certified 875 196 16648066377 (by decide) (by decide +kernel)

private theorem pole_1450_323 :
    P1_7_1.groupedPoleMoment 1450 323 ≤ 124538640464 :=
  _root_.PoleAffine6970.certified 1450 323 124538640464 (by decide) (by decide +kernel)

theorem bank_463_642_142 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨463,642,142,u⟩,3047210090496,4794203956⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree04_bank_checked 463 642 142 u 3047210090496 4794203956
    (by decide) (by decide) (by decide) (by decide) pole_642_142

theorem bank_631_875_196 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨631,875,196,u⟩,7766805577728,16648066377⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree04_bank_checked 631 875 196 u 7766805577728 16648066377
    (by decide) (by decide) (by decide) (by decide) pole_875_196

theorem bank_1045_1450_323 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1045,1450,323,u⟩,35043840884736,124538640464⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree04_bank_checked 1045 1450 323 u 35043840884736 124538640464
    (by decide) (by decide) (by decide) (by decide) pole_1450_323

end Research6970.Height2308.SeedOnePrimary
namespace Research6970.Height2308.SeedOnePrimary
open Research6969

abbrev bank12 : P1_7.Bank := ⟨⟨463,642,142,39647⟩,3047210090496,4794203956⟩
theorem free12 : TransitionSources.Free 2308 51 bank12 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 51 bank12) 2308 = 14361731714400 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 51 bank12) 2309 = 15900700645576320 := by decide +kernel
  refine ⟨bank_463_642_142 39647, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank13 : P1_7.Bank := ⟨⟨631,875,196,7832⟩,7766805577728,16648066377⟩
theorem free13 : TransitionSources.Free 2308 50 bank13 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 50 bank13) 2308 = 34126825225206 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 50 bank13) 2309 = 1581055421975484 := by decide +kernel
  refine ⟨bank_631_875_196 7832, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank14 : P1_7.Bank := ⟨⟨1045,1450,323,13037⟩,35043840884736,124538640464⟩
theorem free14 : TransitionSources.Free 2308 90 bank14 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 90 bank14) 2308 = 464844392000616 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 90 bank14) 2309 = 19319392048001928 := by decide +kernel
  refine ⟨bank_1045_1450_323 13037, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedOnePrimary
end Pack_R6970Height2308SeedOnePrimaryFree04

section Pack_R6970Height2308SeedOnePrimaryFree05

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedOnePrimary

private theorem pack_R6970Height2308SeedOnePrimaryFree05_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_210_41 :
    P1_7_1.groupedPoleMoment 210 41 ≤ 51220963 :=
  _root_.PoleAffine6970.certified 210 41 51220963 (by decide) (by decide +kernel)

private theorem pole_1149_254 :
    P1_7_1.groupedPoleMoment 1149 254 ≤ 48886547370 :=
  _root_.PoleAffine6970.certified 1149 254 48886547370 (by decide) (by decide +kernel)

private theorem pole_1169_258 :
    P1_7_1.groupedPoleMoment 1169 258 ≤ 52307500448 :=
  _root_.PoleAffine6970.certified 1169 258 52307500448 (by decide) (by decide +kernel)

theorem bank_842_1169_258 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨842,1169,258,u⟩,18230973300736,52307500448⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree05_bank_checked 842 1169 258 u 18230973300736 52307500448
    (by decide) (by decide) (by decide) (by decide) pole_1169_258

theorem bank_828_1149_254 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨828,1149,254,u⟩,17353252536320,48886547370⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree05_bank_checked 828 1149 254 u 17353252536320 48886547370
    (by decide) (by decide) (by decide) (by decide) pole_1149_254

theorem bank_151_210_41 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨151,210,41,u⟩,98514239488,51220963⟩ :=
  pack_R6970Height2308SeedOnePrimaryFree05_bank_checked 151 210 41 u 98514239488 51220963
    (by decide) (by decide) (by decide) (by decide) pole_210_41

end Research6970.Height2308.SeedOnePrimary
namespace Research6970.Height2308.SeedOnePrimary
open Research6969

abbrev bank15 : P1_7.Bank := ⟨⟨842,1169,258,97723⟩,18230973300736,52307500448⟩
theorem free15 : TransitionSources.Free 2308 103 bank15 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 103 bank15) 2308 = 76158411285418 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 103 bank15) 2309 = 556732550903027114 := by decide +kernel
  refine ⟨bank_842_1169_258 97723, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank16 : P1_7.Bank := ⟨⟨828,1149,254,184588⟩,17353252536320,48886547370⟩
theorem free16 : TransitionSources.Free 2308 103 bank16 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 103 bank16) 2308 = 85526203748295 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 103 bank16) 2309 = 1890189267575700435 := by decide +kernel
  refine ⟨bank_828_1149_254 184588, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

abbrev bank17 : P1_7.Bank := ⟨⟨151,210,41,4495⟩,98514239488,51220963⟩
theorem free17 : TransitionSources.Free 2308 5 bank17 := by
  have lo : TransitionArithmetic.value (TransitionSources.request 5 bank17) 2308 = 221078926064 := by decide +kernel
  have hi : TransitionArithmetic.value (TransitionSources.request 5 bank17) 2309 = 8242367995888 := by decide +kernel
  refine ⟨bank_151_210_41 4495, by decide, by decide,
    by unfold _root_.Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [lo]; decide
  · rw [lo,hi]; decide

end Research6970.Height2308.SeedOnePrimary
end Pack_R6970Height2308SeedOnePrimaryFree05
