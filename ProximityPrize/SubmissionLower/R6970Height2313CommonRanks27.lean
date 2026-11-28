import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0591

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2929_647 :
    P1_7_1.groupedPoleMoment 2929 647 ≤ 2054078646343 :=
  _root_.PoleAffine6970.certified 2929 647 2054078646343 (by decide) (by decide +kernel)

private theorem pole_2929_649 :
    P1_7_1.groupedPoleMoment 2929 649 ≤ 2059012982891 :=
  _root_.PoleAffine6970.certified 2929 649 2059012982891 (by decide) (by decide +kernel)

private theorem pole_2929_662 :
    P1_7_1.groupedPoleMoment 2929 662 ≤ 2090961110089 :=
  _root_.PoleAffine6970.certified 2929 662 2090961110089 (by decide) (by decide +kernel)

private theorem pole_2930_632 :
    P1_7_1.groupedPoleMoment 2930 632 ≤ 2019119590628 :=
  _root_.Research6969.PackedRanks.PackedRanks252To254.moment2930_632

private theorem pole_2930_633 :
    P1_7_1.groupedPoleMoment 2930 633 ≤ 2021610130172 :=
  _root_.PoleAffine6970.certified 2930 633 2021610130172 (by decide) (by decide +kernel)

private theorem pole_2930_636 :
    P1_7_1.groupedPoleMoment 2930 636 ≤ 2029073656181 :=
  _root_.PoleAffine6970.certified 2930 636 2029073656181 (by decide) (by decide +kernel)

private theorem pole_2930_645 :
    P1_7_1.groupedPoleMoment 2930 645 ≤ 2051392203643 :=
  _root_.Research6969.PackedRanks.PackedRanks252To254.moment2930_645

private theorem pole_2930_646 :
    P1_7_1.groupedPoleMoment 2930 646 ≤ 2053865446192 :=
  _root_.PoleAffine6970.certified 2930 646 2053865446192 (by decide) (by decide +kernel)

private theorem pole_2930_662 :
    P1_7_1.groupedPoleMoment 2930 662 ≤ 2093261903519 :=
  _root_.Research6969.PackedRanks.PackedRanks252To254.moment2930_662

private theorem pole_2932_632 :
    P1_7_1.groupedPoleMoment 2932 632 ≤ 2023557179736 :=
  _root_.PoleAffine6970.certified 2932 632 2023557179736 (by decide) (by decide +kernel)

theorem bank_2110_2929_647 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2110,2929,647,u⟩,286087808286720,2054078646343⟩ :=
  bank_checked 2110 2929 647 u 286087808286720 2054078646343
    (by decide) (by decide) (by decide) (by decide) pole_2929_647

theorem bank_2109_2929_649 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2109,2929,649,u⟩,286454303948800,2059012982891⟩ :=
  bank_checked 2109 2929 649 u 286454303948800 2059012982891
    (by decide) (by decide) (by decide) (by decide) pole_2929_649

theorem bank_2107_2929_662 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2107,2929,662,u⟩,290170711048192,2090961110089⟩ :=
  bank_checked 2107 2929 662 u 290170711048192 2090961110089
    (by decide) (by decide) (by decide) (by decide) pole_2929_662

theorem bank_2105_2929_662 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2105,2929,662,u⟩,289553542021120,2090961110089⟩ :=
  bank_checked 2105 2929 662 u 289553542021120 2090961110089
    (by decide) (by decide) (by decide) (by decide) pole_2929_662

theorem bank_2103_2929_662 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2103,2929,662,u⟩,288937068199936,2090961110089⟩ :=
  bank_checked 2103 2929 662 u 288937068199936 2090961110089
    (by decide) (by decide) (by decide) (by decide) pole_2929_662

theorem bank_2102_2930_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2102,2930,632,u⟩,278652894052352,2019119590628⟩ :=
  bank_checked 2102 2930 632 u 278652894052352 2019119590628
    (by decide) (by decide) (by decide) (by decide) pole_2930_632

theorem bank_2104_2930_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2104,2930,632,u⟩,279246119370752,2019119590628⟩ :=
  bank_checked 2104 2930 632 u 279246119370752 2019119590628
    (by decide) (by decide) (by decide) (by decide) pole_2930_632

theorem bank_2105_2930_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2105,2930,632,u⟩,279542980935680,2019119590628⟩ :=
  bank_checked 2105 2930 632 u 279542980935680 2019119590628
    (by decide) (by decide) (by decide) (by decide) pole_2930_632

theorem bank_2101_2930_633 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2101,2930,633,u⟩,278691788095488,2021610130172⟩ :=
  bank_checked 2101 2930 633 u 278691788095488 2021610130172
    (by decide) (by decide) (by decide) (by decide) pole_2930_633

theorem bank_2101_2930_636 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2101,2930,636,u⟩,279696251813888,2029073656181⟩ :=
  bank_checked 2101 2930 636 u 279696251813888 2029073656181
    (by decide) (by decide) (by decide) (by decide) pole_2930_636

theorem bank_2109_2930_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2109,2930,645,u⟩,285113516032000,2051392203643⟩ :=
  bank_checked 2109 2930 645 u 285113516032000 2051392203643
    (by decide) (by decide) (by decide) (by decide) pole_2930_645

theorem bank_2105_2930_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2105,2930,645,u⟩,283904392560640,2051392203643⟩ :=
  bank_checked 2105 2930 645 u 283904392560640 2051392203643
    (by decide) (by decide) (by decide) (by decide) pole_2930_645

theorem bank_2110_2930_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2110,2930,645,u⟩,285416220262400,2051392203643⟩ :=
  bank_checked 2110 2930 645 u 285416220262400 2051392203643
    (by decide) (by decide) (by decide) (by decide) pole_2930_645

theorem bank_2101_2930_645 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2101,2930,645,u⟩,282697978609664,2051392203643⟩ :=
  bank_checked 2101 2930 645 u 282697978609664 2051392203643
    (by decide) (by decide) (by decide) (by decide) pole_2930_645

theorem bank_2110_2930_646 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2110,2930,646,u⟩,285752121360384,2053865446192⟩ :=
  bank_checked 2110 2930 646 u 285752121360384 2053865446192
    (by decide) (by decide) (by decide) (by decide) pole_2930_646

theorem bank_2110_2930_662 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2110,2930,662,u⟩,291097768099840,2093261903519⟩ :=
  bank_checked 2110 2930 662 u 291097768099840 2093261903519
    (by decide) (by decide) (by decide) (by decide) pole_2930_662

theorem bank_2103_2932_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2103,2932,632,u⟩,278949423742976,2023557179736⟩ :=
  bank_checked 2103 2932 632 u 278949423742976 2023557179736
    (by decide) (by decide) (by decide) (by decide) pole_2932_632

theorem bank_2102_2932_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2102,2932,632,u⟩,278652894052352,2023557179736⟩ :=
  bank_checked 2102 2932 632 u 278652894052352 2023557179736
    (by decide) (by decide) (by decide) (by decide) pole_2932_632

end Research6970.Height2313.CommonBankRanks
