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

private theorem pole_4184_900 :
    P1_7_1.groupedPoleMoment 4184 900 ≤ 8370437628682 :=
  _root_.PoleAffine6970.certified 4184 900 8370437628682 (by decide) (by decide +kernel)

theorem bank_2998_4184_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2998,4184,900,u⟩,806961139154944,8370437628682⟩ :=
  bank_checked 2998 4184 900 u 806961139154944 8370437628682
    (by decide) (by decide) (by decide) (by decide) pole_4184_900

end Research6970.Height2313.Research6969.Geometry2308
