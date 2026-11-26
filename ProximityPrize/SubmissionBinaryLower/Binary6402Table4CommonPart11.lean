import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart10
import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.Binary6402IntFarkas
import ProximityPrize.SubmissionBinaryLower.Binary6402T4Rows
import ProximityPrize.SubmissionBinaryLower.P64Resultant
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 1024

/-!
# Table 4 Common `ker(D)` `(d₁ = 4, d₀ ≤ 5)` Algebra, Resultant Bounds, `det`, and `p0_zero`

Provides the shared algebraic foundation for all 120 Table 4 branches (`B6401Table4NonK` and
`B6401Table4K`), plus complete proofs for `T4ABranch.det` and `T4ABranch.p0Zero`:
1. `SparseRow` / `baseT4Rows` satisfaction bridge matching `B6402IntFarkas.checkT4Bucket_sound`
   and `B6402T4Rows.buildT4ARows` / `buildT4BRows` definitionally.
2. Exact char-2 polynomial helpers (`sqrtPoly`, `evenPart`, `oddPart`, `sum_ord_le_natDegree`).
3. Extraction of `P_j, C_j, B_j, g_j` (`j : Fin 3`) from `f_coord : KerDIdx wY W_F 1 → Fld`
   (`W_F < 6 * wY - 1`), exact degree bounds, and shifted `(A0_j, A1_j, B^{sh}_j)` local orders.
4. Universal formal `(5, 4)` Sylvester resultant theorems:
   - `f1_eval_P_ne_zero`,
   - `natDegree_resultant_5_4_le_sylvester` (`deg_X(Res_Y) ≤ 8 W_F - 20 wY + 4 + deg_X(g_4)`),
   - `pow_dvd_resultant_5_4_U0` (`1, 11, 29 + 18(k - 3)`) and `_U1` (`4, 16, 34 + 18(k - 3)`).
5. `T4ABranch.det` (`det M ≠ 0`) and `T4ABranch.p0Zero` (`det M = 0, p = 0`) satisfaction proofs.
6. `KerD45Syzygy` (`det M = 0, p ≠ 0, U(X, P) ≠ 0`): exact coprime `(p, c, b)`, reduced minors
   `M21, M20, M10`, `Res_Y = H1 * Q2(X^2)^2`, squarefree `D2 = gcd(p, q)` & `D1 = sqrtPoly D2`,
   `D1 ∣ g_j, R, U_P`, `D1^5 ∣ H1`, all shifted local order bounds, and all degree bounds.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402Table4Common

open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401Params hiding A D
open B6402HybridP64 (A)
open B6401KerDOrders B6402IntFarkas B6402T4Rows
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators
local notation (priority := high) "X" => Polynomial.X

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
namespace KerD45Data
variable (D : KerD45Data)

theorem detResRow6402 : RowSatLe D.detCoordinates6402 (mkStat [(1,cI 1),(2,cI 11),(3,cI 29),(4,cI 18),(9,cH (-9))] (-50)) := detResRow6402Numeric D.n0 D.n1 D.n2 D.n3 D.nt D.a0 D.a1 D.a2 D.a3 D.W_F D.hWF_lo (D.resOrdU0_le_natDegree.trans D.natDegree_ResY_le)

theorem detDegreeRow6402Numeric (n0 n1 n2 n3 nt a0 a1 a2 a3 W_F : ℕ) (hwf : 5*wY≤W_F+1) (hDetB : 2 * (2 * n2 + 5 * n3 + 3 * nt) ≤ 3 * W_F - 8 * wY + 1) : RowSatLe (rawDetCoordinates n0 n1 n2 n3 nt a0 a1 a2 a3 W_F) (mkStat [(2,cI 2),(3,cI 5),(4,cI 3),(9,cQ (-3))] (-8)) := by
  have hc_nn : (0 : ℚ) ≤ (W_F : ℚ) / (wY : ℚ) := by positivity
  have hN_eq : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  rw [rowSatLe_mkStat_iff]
  simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    show (2 : ℕ) < 10 by decide, show (3 : ℕ) < 10 by decide, show (4 : ℕ) < 10 by decide,
    show (9 : ℕ) < 10 by decide, ↓reduceDIte, ↓reduceIte, rawDetCoordinates, cI_mul_div_N, cQ_mul_c_eq]
  have hDetQ : 2 * (2 * (n2 : ℚ) + 5 * (n3 : ℚ) + 3 * (nt : ℚ)) ≤
      3 * (W_F : ℚ) - 8 * (wY : ℚ) + 1 := by
    have h8 : 8 * wY ≤ 3 * W_F := by have := hwf; have := (by decide : 0<wY); omega
    have hZ : ((2 * (2 * n2 + 5 * n3 + 3 * nt) : ℕ) : ℤ) ≤ 3 * (W_F : ℤ) - 8 * (wY : ℤ) + 1 := by clear * - hDetB h8; omega
    exact_mod_cast hZ
  push_cast; rw [hN_eq]; linarith only [hDetQ,hc_nn]

end KerD45Data
end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
