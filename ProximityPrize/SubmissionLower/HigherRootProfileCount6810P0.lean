import ProximityPrize.SubmissionLower.HigherRootAsymmetric6810P0
import ProximityPrize.SubmissionLower.HigherRootSources6810

namespace ProximityPrize.SubmissionLower.HigherRootProfileCount6810P0
open HigherRootNumericGeometry6810P0 RCN260 RCN294 RCN135
open HigherRootRegularData6810P0 HigherRootRegularData6810P0.Data HigherRootOwnShape6810P0
open HigherRootSources6810.P0 (exists_interpolant)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

theorem uniform_gates (r y t R U T : ℕ)
    (hr : r ≤ 31) (hy : y ≤ 142) (ht : t ≤ 7501)
    (hR : R ≤ 774) (hU : U ≤ 3564) (hT : T ≤ 181800) :
    (parameters r y t R U T).mixedCost.y < 2130706433 ∧
    (parameters r y t R U T).mixedCost.r < 2130706433 ∧
    (parameters r y t R U T).mixedCost.z < 2130706433 := by
  have h := mixed_mono hr hy ht hR hU hT
  exact ⟨h.1.trans_lt (by norm_num [parameters,UnequalParameters.mixedCost]),
    h.2.1.trans_lt (by norm_num [parameters,UnequalParameters.mixedCost]),
    h.2.2.trans_lt (by norm_num [parameters,UnequalParameters.mixedCost])⟩

theorem helper_gates (S : Data nodes u0 u1) :
    S.PairGates (54+24*(S.r-1)) (180+24*(S.y-1)) (1800+24*(S.t-1)) := by
  apply uniform_gates _ _ _ _ _ _ S.rbound S.ybound S.tbound
  · have := S.rbound
    omega
  · have := S.ybound
    omega
  · have := S.tbound
    omega

theorem coefficient_gates (S : Data nodes u0 u1) : S.PairGates 54 180 1800 :=
  uniform_gates _ _ _ _ _ _ S.rbound S.ybound S.tbound (by decide) (by decide) (by decide)

/-- The root source is constructed from the node data; all exceptional branches
are paid. No helper divisibility, proper-first-tail, good-point, or identity-cost
premise is left to the caller. -/
theorem count_profile (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hL : 1800 < RCN234.wt RCN156.residualTotalWeights S.F) :
    S.seeds.card ≤ HigherRootAsymmetric6810P0.bound S := by
  obtain ⟨P,hP⟩ := exists_interpolant (nodes := nodes) (u0 := u0) (u1 := u1) hI
  exact HigherRootAsymmetric6810P0.count_of_interpolant_total S hI P hP hL
    (fun d hd => factorial_ne (K := K) d (by omega))
    (two_ne (K := GenericField K)) (factorial_ne (K := GenericField K) 5 (by decide))
    (helper_gates S) (coefficient_gates S)

end
end ProximityPrize.SubmissionLower.HigherRootProfileCount6810P0
