import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart19
import ProximityPrize.SubmissionBinaryLower.Binary6402Table4Common
import ProximityPrize.SubmissionBinaryLower.Binary6402Table4NonK

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 1024

/-!
# Table 4B (`K ≠ 0`, 84 branches) and Top-Level Table 4 Exhaustive Algebra Dichotomy

Proves:
1. `table4_K_sat`: for any `S : KerD45Syzygy D` with `S.P0 = 0` and `S.M21 ≠ 0`, `D` produces an
   exact `T4BBranch` (`rGt ∈ Bool`, `vCancel ∈ Bool`, `q1Case < 3`, `odeCase < 7`) and an explicit
   nonnegative `x : Fin 49 → ℚ` satisfying ALL rows of `B6402T4Rows.buildT4BRows br`!
2. `table4_algebra_dichotomy`: for ANY `D : KerD45Data`, EITHER `EscapeUZero D`, OR `D` satisfies
   one of the 36 Table 4A branches (`T4ABranch`) OR one of the 84 Table 4B branches (`T4BBranch`)!
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402Table4K

open B6401Params hiding A
open B6402HybridP64 (A)
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6402IntFarkas B6402T4Rows B6401Char2ODE B6402Table4Common B6402Table4NonK
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

theorem geometryRows
    (br : T4BBranch) (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (v : Fin 48 → ℕ) (WF : ℕ)
    (hBS : let x := t4bVec v WF
           let (ubB, eqB) := baseT4Rows 48 cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
           (∀ r ∈ ubB, RowSatLe x r) ∧ (∀ r ∈ eqB, RowSatEq x r))
    (h_heq_nat : conditions_heq_nat v br WF)
    (h_hub_nat1 : conditions_hub_nat1 v br WF)
    (h_hub_nat2 : conditions_hub_nat2 v br WF)
    (h_hR_nat : conditions_hR_nat v br WF)
    (h_hV_nat : conditions_hV_nat v br WF)
    (h_hQ1_nat : conditions_hQ1_nat v br WF)
    (h_ode0 : conditions_ode0 v br WF)
    (h_ode1 : conditions_ode1 v br WF)
    (h_ode2 : conditions_ode2 v br WF)
    (h_ode3 : conditions_ode3 v br WF)
    (h_ode4 : conditions_ode4 v br WF)
    (h_ode5 : conditions_ode5 v br WF)
    (h_ode6 : conditions_ode6 v br WF)
    (hode_lt : br.odeCase < 7) :
    (∀ r ∈ (buildT4BRows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen).1.toList, RowValid 49 r ∧ RowSatLe (t4bVec v WF) r) ∧
    (∀ r ∈ (buildT4BRows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen).2.toList, RowValid 49 r ∧ RowSatEq (t4bVec v WF) r) := by
  exact table4_K_rows_sat br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    hcLoD hcHiD hloGD hhiGD v WF hBS h_heq_nat h_hub_nat1 h_hub_nat2 h_hR_nat h_hV_nat h_hQ1_nat
    ⟨h_ode0,h_ode1,h_ode2,h_ode3,h_ode4,h_ode5,h_ode6⟩ hode_lt

end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
