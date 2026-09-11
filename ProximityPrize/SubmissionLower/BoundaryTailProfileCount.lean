import ProximityPrize.SubmissionLower.BoundaryTailAsymmetric
import ProximityPrize.SubmissionLower.BoundaryTailProfile116

namespace ProximityPrize.SubmissionLower.BoundaryTailProfileCount
open BoundaryTailNumericGeometry RCN260 RCN294 RCN135
open BoundaryTailRegularData BoundaryTailRegularData.Data BoundaryTailOwnShape
open BoundaryTailProfile116 (exists_interpolant)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

theorem uniform_gates (r y t R U T : ℕ)
    (hr : r ≤ 30) (hy : y ≤ 139) (ht : t ≤ 7199)
    (hR : R ≤ 656) (hU : U ≤ 3055) (hT : T ≤ 153444) :
    (parameters r y t R U T).mixedCost.y < 2130706433 ∧
    (parameters r y t R U T).mixedCost.r < 2130706433 ∧
    (parameters r y t R U T).mixedCost.z < 2130706433 := by
  have h := mixed_mono hr hy ht hR hU hT
  exact ⟨h.1.trans_lt (by norm_num [parameters,UnequalParameters.mixedCost]),
    h.2.1.trans_lt (by norm_num [parameters,UnequalParameters.mixedCost]),
    h.2.2.trans_lt (by norm_num [parameters,UnequalParameters.mixedCost])⟩

theorem helper_gates (S : Data nodes u0 u1) :
    S.PairGates (47+21*(S.r-1)) (157+21*(S.y-1)) (2286+21*(S.t-1)) := by
  apply uniform_gates _ _ _ _ _ _ S.rbound S.ybound S.tbound
  · have := S.rbound
    omega
  · have := S.ybound
    omega
  · have := S.tbound
    omega

theorem coefficient_gates (S : Data nodes u0 u1) : S.PairGates 47 157 2286 :=
  uniform_gates _ _ _ _ _ _ S.rbound S.ybound S.tbound (by decide) (by decide) (by decide)

theorem count_116 (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hown : Own S) (hL : 2286 < S.t) :
    S.seeds.card ≤ BoundaryTailAsymmetric.numericBound S.r (S.y-S.r) (S.t-S.y)
      47 157 2286 21 5 7 := by
  obtain ⟨P,hP⟩ := exists_interpolant (nodes := nodes) (u0 := u0) (u1 := u1) hI
  have hc := BoundaryTailAsymmetric.count_of_interpolant_total S hI P 116 47 21 157 2286 5 7 hP
    (avoidance_total S hown _ hL)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun d hd => factorial_ne (K := K) d (by omega))
    (two_ne (K := GenericField K)) (factorial_ne (K := GenericField K) 5 (by decide))
    (helper_gates S) (coefficient_gates S)
  rwa [BoundaryTailAsymmetric.bound_eq_numeric S hown] at hc

end
end ProximityPrize.SubmissionLower.BoundaryTailProfileCount
