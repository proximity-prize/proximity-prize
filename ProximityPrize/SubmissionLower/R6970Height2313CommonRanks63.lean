import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0604

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

private theorem pole_6665_1474 :
    P1_7_1.groupedPoleMoment 6665 1474 ≤ 55035799050931 :=
  _root_.PoleAffine6970.certified 6665 1474 55035799050931 (by decide) (by decide +kernel)

private theorem pole_6681_1449 :
    P1_7_1.groupedPoleMoment 6681 1449 ≤ 54728084477665 :=
  _root_.PoleAffine6970.certified 6681 1449 54728084477665 (by decide) (by decide +kernel)

private theorem pole_6682_1437 :
    P1_7_1.groupedPoleMoment 6682 1437 ≤ 54400253472283 :=
  _root_.PoleAffine6970.certified 6682 1437 54400253472283 (by decide) (by decide +kernel)

private theorem pole_6682_1445 :
    P1_7_1.groupedPoleMoment 6682 1445 ≤ 54636500602517 :=
  _root_.PoleAffine6970.certified 6682 1445 54636500602517 (by decide) (by decide +kernel)

private theorem pole_6682_1474 :
    P1_7_1.groupedPoleMoment 6682 1474 ≤ 55489160567431 :=
  _root_.PoleAffine6970.certified 6682 1474 55489160567431 (by decide) (by decide +kernel)

private theorem pole_6686_1445 :
    P1_7_1.groupedPoleMoment 6686 1445 ≤ 54741834824859 :=
  _root_.PoleAffine6970.certified 6686 1445 54741834824859 (by decide) (by decide +kernel)

private theorem pole_6689_1453 :
    P1_7_1.groupedPoleMoment 6689 1453 ≤ 55057550828510 :=
  _root_.PoleAffine6970.certified 6689 1453 55057550828510 (by decide) (by decide +kernel)

private theorem pole_6690_1445 :
    P1_7_1.groupedPoleMoment 6690 1445 ≤ 54847307041873 :=
  _root_.PoleAffine6970.certified 6690 1445 54847307041873 (by decide) (by decide +kernel)

private theorem pole_6692_1474 :
    P1_7_1.groupedPoleMoment 6692 1474 ≤ 55757027345056 :=
  _root_.Research6969.PackedRanks.PackedRanks318To320.moment6692_1474

private theorem pole_6692_1490 :
    P1_7_1.groupedPoleMoment 6692 1490 ≤ 56227346640330 :=
  _root_.PoleAffine6970.certified 6692 1490 56227346640330 (by decide) (by decide +kernel)

theorem bank_4800_6665_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4800,6665,1474,u⟩,3367547627110400,55035799050931⟩ :=
  bank_checked 4800 6665 1474 u 3367547627110400 55035799050931
    (by decide) (by decide) (by decide) (by decide) pole_6665_1474

theorem bank_4800_6681_1449 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4800,6681,1449,u⟩,3324016676044800,54728084477665⟩ :=
  bank_checked 4800 6681 1449 u 3324016676044800 54728084477665
    (by decide) (by decide) (by decide) (by decide) pole_6681_1449

theorem bank_4788_6682_1437 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4788,6682,1437,u⟩,3284573675585536,54400253472283⟩ :=
  bank_checked 4788 6682 1437 u 3284573675585536 54400253472283
    (by decide) (by decide) (by decide) (by decide) pole_6682_1437

theorem bank_4792_6682_1445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4792,6682,1445,u⟩,3304668702441472,54636500602517⟩ :=
  bank_checked 4792 6682 1445 u 3304668702441472 54636500602517
    (by decide) (by decide) (by decide) (by decide) pole_6682_1445

theorem bank_4802_6682_1445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4802,6682,1445,u⟩,3320115406569472,54636500602517⟩ :=
  bank_checked 4802 6682 1445 u 3320115406569472 54636500602517
    (by decide) (by decide) (by decide) (by decide) pole_6682_1445

theorem bank_4801_6682_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4801,6682,1474,u⟩,3369119023104000,55489160567431⟩ :=
  bank_checked 4801 6682 1474 u 3369119023104000 55489160567431
    (by decide) (by decide) (by decide) (by decide) pole_6682_1474

theorem bank_4805_6686_1445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4805,6686,1445,u⟩,3324756809482240,54741834824859⟩ :=
  bank_checked 4805 6686 1445 u 3324756809482240 54741834824859
    (by decide) (by decide) (by decide) (by decide) pole_6686_1445

theorem bank_4807_6689_1453 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4807,6689,1453,u⟩,3341881529860096,55057550828510⟩ :=
  bank_checked 4807 6689 1453 u 3341881529860096 55057550828510
    (by decide) (by decide) (by decide) (by decide) pole_6689_1453

theorem bank_4798_6690_1445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4798,6690,1445,u⟩,3313932176195584,54847307041873⟩ :=
  bank_checked 4798 6690 1445 u 3313932176195584 54847307041873
    (by decide) (by decide) (by decide) (by decide) pole_6690_1445

theorem bank_4812_6692_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4812,6692,1474,u⟩,3386429898752000,55757027345056⟩ :=
  bank_checked 4812 6692 1474 u 3386429898752000 55757027345056
    (by decide) (by decide) (by decide) (by decide) pole_6692_1474

theorem bank_4822_6692_1490 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4822,6692,1490,u⟩,3430214978240512,56227346640330⟩ :=
  bank_checked 4822 6692 1490 u 3430214978240512 56227346640330
    (by decide) (by decide) (by decide) (by decide) pole_6692_1490

end Research6970.Height2313.CommonBankRanks
