/- P33Bridge (Bome2017 tree): a residual factor of a `K6833Residual.TerminalData` inside a packet window has
fiber ≤ cap. Same proof as the 68.32 version (Ready/ReachedTerminal), with the TerminalData fields:
seeds/selected/u₀/u₁/degree/agreement (181059)/pencil (81085) and the primary cutoff 57757821. -/
import ProximityPrize.SubmissionLower.P33Windows
import ProximityPrize.SubmissionLower.K6833TerminalData

namespace ProximityPrize
namespace SubmissionLower
namespace P33
open scoped Classical BigOperators
open RCN095 RCN130 RCN156 RCN167 RCN174 RCN234 RCN238 RCN266 RCN275 RCN286 RCN313
open LocatorHybridCells LocatorFactorAggregate LocatorBatchProductRoute
open Koala6831MovingPaid K6833Residual
set_option autoImplicit false

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq K]

theorem regularFiber_eq_regularSeeds (H : MvPolynomial (Fin 4) K) (selected : K → Polynomial K) (Γ : Finset K)
    (F : RegularIndex H) :
    regularFiber H Γ selected F = RCN140.regularSeeds H selected Γ F := by
  ext γ
  rw [mem_regularFiber, RCN140.regularSeeds, Finset.mem_filter]
  exact Iff.rfl

/-- **fiber_le_window** for Bome2017's `TerminalData` (K6833TerminalData.lean:19). -/
theorem fiber_le_window {x : I ↪ K} (T : TerminalData x)
    (W : Window) (hW : WindowCount W) (hr5 : 5 ≤ W.r) (hrh : W.r ≤ 14) (hy : W.r + 2 ≤ W.y) (hyh : W.y ≤ 71)
    (hyt : W.y ≤ W.t) (hth : W.t ≤ 7200)
    (F : RegularIndex T.primary)
    (f : Envelope) (hdata : ResidualSupportData (f.paddedSupport 0) F.1)
    (hr : wt residualSWeights F.1 ≤ W.r) (hyF : wt residualYSWeights F.1 ≤ W.y)
    (ht : wt residualTotalWeights F.1 ≤ W.t) (hlow : W.low ≤ wt residualTotalWeights F.1) :
    (regularFiber T.primary T.seeds T.selected F).card ≤ W.cap := by
  have hbox := T.factor_global_box F hdata
  let P := CVL.factorPacket F 57757821 _ _ W.t W.y W.r (by norm_num) (by norm_num) hbox hr5 hrh hy hyh hyt hth
    hr hyF ht x T.u₀ T.u₁ T.nodes_card T.selected T.seeds T.degree
    (fun γ hγ => by have h := T.agreement γ hγ; convert h)
    (fun P₀ P₁ h₀ h₁ => (T.pencil P₀ P₁ h₀ h₁).trans (by norm_num))
  have hseeds : P.seeds = RCN140.regularSeeds T.primary T.selected T.seeds F := rfl
  have hPF : P.F = F.1 := rfl
  have hcount := hW x T.nodes_card P (by rw [hPF]; exact hlow)
  rw [regularFiber_eq_regularSeeds, ← hseeds]
  exact hcount

end P33
end SubmissionLower
end ProximityPrize
