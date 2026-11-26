import ProximityPrize.SubmissionBinaryLower.Binary6402Table4KPart21
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

attribute [local irreducible] buildT4BRows baseT4Rows
theorem geometryFromData {D : KerD45Data} (S : KerD45Syzygy D) (K : KerD45KData S)
    (c0 c1 : Fld) (L : Fld[X]) (hc0 : c0≠0)
    (hNdom_eq : Ndom=C c0*X+C c1*X^2+L^4) (hNdom_deg : Ndom.natDegree=N)
    (hL4 : 4*L.natDegree=N) (hd1 : Ndom.derivative=C c0) (hd2 : hasse 2 Ndom=C c1)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ))
    (hcHi : (D.W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (hloG : (loGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≥ (loGNum * N : ℤ))
    (hhiG : hiGNum < hiGDen → (hiGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≤ (hiGNum * N : ℤ)) :
    ∃ br : T4BBranch, br.q1Case < 3 ∧ br.odeCase < 7 ∧
      let rows := buildT4BRows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
      ∃ x : Fin 49 → ℚ,
        (∀ j, 0 ≤ x j) ∧
        x ⟨0, by decide⟩ = (D.n0 : ℚ) / (N : ℚ) ∧ x ⟨1, by decide⟩ = (D.n1 : ℚ) / (N : ℚ) ∧
        x ⟨2, by decide⟩ = (D.n2 : ℚ) / (N : ℚ) ∧ x ⟨3, by decide⟩ = (D.n3 : ℚ) / (N : ℚ) ∧
        x ⟨4, by decide⟩ = (D.nt : ℚ) / (N : ℚ) ∧ x ⟨48, by decide⟩ = (D.W_F : ℚ) / (wY : ℚ) ∧
        (∀ r ∈ rows.1.toList, RowValid 49 r ∧ RowSatLe x r) ∧
        (∀ r ∈ rows.2.toList, RowValid 49 r ∧ RowSatEq x r) := by
  classical
  let v := geometryVec S K
  let br := geometryBranch S K c0 c1
  let x := t4bVec v D.W_F
  have hq1_lt := (geometryBranch_bounds S K c0 c1).1
  have hode_lt := (geometryBranch_bounds S K c0 c1).2
  refine ⟨br, hq1_lt, hode_lt, x, geometryNonneg S K, (geometryCoord0 S K), (geometryCoord1 S K), (geometryCoord2 S K), (geometryCoord3 S K), (geometryCoord4 S K), (geometryCoord9 S K), ?_⟩
  have hBS := D.baseT4Rows_sat (nv := 49) (ic := 48) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD x
    (geometryCoord0 S K) (geometryCoord1 S K) (geometryCoord2 S K) (geometryCoord3 S K) (geometryCoord4 S K) (geometryCoord5 S K) (geometryCoord6 S K) (geometryCoord7 S K) (geometryCoord8 S K) (geometryCoord9 S K) hcLo hcHi hloG hhiG
  have sat := geometryRows br cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    hcLoD hcHiD hloGD hhiGD v D.W_F hBS
    (geometry_heq_nat S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1)
    (geometry_hub_nat1 S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1)
    (geometry_hub_nat2 S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1)
    (geometry_hR_nat S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1)
    (geometry_hV_nat S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1)
    (geometry_hQ1_nat S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1)
    (geometry_ode0 S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1)
    (geometry_ode1 S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1 hd2)
    (geometry_ode2 S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1)
    (geometry_ode3 S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1)
    (geometry_ode4 S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1)
    (geometry_ode5 S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1)
    (geometry_ode6 S K c0 c1 L hc0 hNdom_eq hNdom_deg hL4 hd1)
    hode_lt
  exact sat

end B6402Table4K
end ProximityPrize.SubmissionBinaryLower
