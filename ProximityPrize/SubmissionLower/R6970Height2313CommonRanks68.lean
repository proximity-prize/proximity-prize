import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0612
import ProximityPrize.SubmissionLower.Z6969Pack0613

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

private theorem pole_7950_1796 :
    P1_7_1.groupedPoleMoment 7950 1796 ≤ 113242283843565 :=
  _root_.Research6969.PackedRanks.PackedRanks339To341.moment7950_1796

private theorem pole_7951_1750 :
    P1_7_1.groupedPoleMoment 7951 1750 ≤ 111025751789870 :=
  _root_.Research6969.PackedRanks.PackedRanks339To341.moment7951_1750

private theorem pole_7951_1796 :
    P1_7_1.groupedPoleMoment 7951 1796 ≤ 113288194826317 :=
  _root_.Research6969.PackedRanks.PackedRanks339To341.moment7951_1796

private theorem pole_7952_1728 :
    P1_7_1.groupedPoleMoment 7952 1728 ≤ 109981062065525 :=
  _root_.PoleAffine6970.certified 7952 1728 109981062065525 (by decide) (by decide +kernel)

private theorem pole_7952_1732 :
    P1_7_1.groupedPoleMoment 7952 1732 ≤ 110179534728296 :=
  _root_.PoleAffine6970.certified 7952 1732 110179534728296 (by decide) (by decide +kernel)

private theorem pole_7952_1796 :
    P1_7_1.groupedPoleMoment 7952 1796 ≤ 113334118485107 :=
  _root_.Research6969.PackedRanks.PackedRanks342To344.moment7952_1796

private theorem pole_7953_1716 :
    P1_7_1.groupedPoleMoment 7953 1716 ≤ 109428971647179 :=
  _root_.Research6969.PackedRanks.PackedRanks345To347.moment7953_1716

private theorem pole_7953_1724 :
    P1_7_1.groupedPoleMoment 7953 1724 ≤ 109826875558354 :=
  _root_.PoleAffine6970.certified 7953 1724 109826875558354 (by decide) (by decide +kernel)

private theorem pole_7953_1750 :
    P1_7_1.groupedPoleMoment 7953 1750 ≤ 111115710437454 :=
  _root_.Research6969.PackedRanks.PackedRanks345To347.moment7953_1750

private theorem pole_7954_1716 :
    P1_7_1.groupedPoleMoment 7954 1716 ≤ 109473260530676 :=
  _root_.Research6969.PackedRanks.PackedRanks345To347.moment7954_1716

theorem bank_5733_7950_1796 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5733,7950,1796,u⟩,5824240852664320,113242283843565⟩ :=
  bank_checked 5733 7950 1796 u 5824240852664320 113242283843565
    (by decide) (by decide) (by decide) (by decide) pole_7950_1796

theorem bank_5707_7951_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5707,7951,1750,u⟩,5652886789292032,111025751789870⟩ :=
  bank_checked 5707 7951 1750 u 5652886789292032 111025751789870
    (by decide) (by decide) (by decide) (by decide) pole_7951_1750

theorem bank_5718_7951_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5718,7951,1750,u⟩,5677314604007424,111025751789870⟩ :=
  bank_checked 5718 7951 1750 u 5677314604007424 111025751789870
    (by decide) (by decide) (by decide) (by decide) pole_7951_1750

theorem bank_5708_7951_1796 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5708,7951,1796,u⟩,5767441253662720,113288194826317⟩ :=
  bank_checked 5708 7951 1796 u 5767441253662720 113288194826317
    (by decide) (by decide) (by decide) (by decide) pole_7951_1796

theorem bank_5725_7951_1796 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5725,7951,1796,u⟩,5806032948035584,113288194826317⟩ :=
  bank_checked 5725 7951 1796 u 5806032948035584 113288194826317
    (by decide) (by decide) (by decide) (by decide) pole_7951_1796

theorem bank_5715_7952_1728 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5715,7952,1728,u⟩,5616331038130176,109981062065525⟩ :=
  bank_checked 5715 7952 1728 u 5616331038130176 109981062065525
    (by decide) (by decide) (by decide) (by decide) pole_7952_1728

theorem bank_5717_7952_1732 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5717,7952,1732,u⟩,5630634927849472,110179534728296⟩ :=
  bank_checked 5717 7952 1732 u 5630634927849472 110179534728296
    (by decide) (by decide) (by decide) (by decide) pole_7952_1732

theorem bank_5726_7952_1796 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5726,7952,1796,u⟩,5808307287359488,113334118485107⟩ :=
  bank_checked 5726 7952 1796 u 5808307287359488 113334118485107
    (by decide) (by decide) (by decide) (by decide) pole_7952_1796

theorem bank_5714_7953_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5714,7953,1716,u⟩,5584397632012288,109428971647179⟩ :=
  bank_checked 5714 7953 1716 u 5584397632012288 109428971647179
    (by decide) (by decide) (by decide) (by decide) pole_7953_1716

theorem bank_5722_7953_1724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5722,7953,1724,u⟩,5621799092224000,109826875558354⟩ :=
  bank_checked 5722 7953 1724 u 5621799092224000 109826875558354
    (by decide) (by decide) (by decide) (by decide) pole_7953_1724

theorem bank_5725_7953_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5725,7953,1750,u⟩,5692888494899200,111115710437454⟩ :=
  bank_checked 5725 7953 1750 u 5692888494899200 111115710437454
    (by decide) (by decide) (by decide) (by decide) pole_7953_1750

theorem bank_5726_7953_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5726,7953,1750,u⟩,5695115172511744,111115710437454⟩ :=
  bank_checked 5726 7953 1750 u 5695115172511744 111115710437454
    (by decide) (by decide) (by decide) (by decide) pole_7953_1750

theorem bank_5705_7954_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5705,7954,1716,u⟩,5564742610714624,109473260530676⟩ :=
  bank_checked 5705 7954 1716 u 5564742610714624 109473260530676
    (by decide) (by decide) (by decide) (by decide) pole_7954_1716

theorem bank_5704_7954_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5704,7954,1716,u⟩,5562560969965568,109473260530676⟩ :=
  bank_checked 5704 7954 1716 u 5562560969965568 109473260530676
    (by decide) (by decide) (by decide) (by decide) pole_7954_1716

end Research6970.Height2313.CommonBankRanks
