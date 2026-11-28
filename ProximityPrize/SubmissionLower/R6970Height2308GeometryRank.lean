import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.Geometry2308

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

private theorem pole_4080_900 :
    P1_7_1.groupedPoleMoment 4080 900 ≤ 7719024287402 :=
  _root_.PoleAffine6970.certified 4080 900 7719024287402 (by decide) (by decide +kernel)

private theorem pole_4162_900 :
    P1_7_1.groupedPoleMoment 4162 900 ≤ 8229637344156 :=
  _root_.PoleAffine6970.certified 4162 900 8229637344156 (by decide) (by decide +kernel)

theorem bank_2933_4080_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2933,4080,900,u⟩,768334341341184,7719024287402⟩ :=
  bank_checked 2933 4080 900 u 768334341341184 7719024287402
    (by decide) (by decide) (by decide) (by decide) pole_4080_900

theorem bank_2987_4162_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2987,4162,900,u⟩,800354147500032,8229637344156⟩ :=
  bank_checked 2987 4162 900 u 800354147500032 8229637344156
    (by decide) (by decide) (by decide) (by decide) pole_4162_900

end Research6970.Height2313.Research6969.Geometry2308
