import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart3
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

theorem pow_dvd_ResY_U0 (i : Idx) :
    (X - C (BinaryIRSProfile.domain i)) ^ resOrdU0 (D.k i) ∣ D.ResY := by
  simpa using D.pow_dvd_ResY_general i 0 (by omega) fun j => (D.local_shifted_ords i j).2.2

/-! ### Part 5: Common Point Counts & `baseT4Rows` Satisfaction -/

noncomputable def n0 (D : KerD45Data) : ℕ := (Finset.univ.filter fun i : Idx => D.k i = 0).card
noncomputable def n1 (D : KerD45Data) : ℕ := (Finset.univ.filter fun i : Idx => D.k i = 1).card
noncomputable def n2 (D : KerD45Data) : ℕ := (Finset.univ.filter fun i : Idx => D.k i = 2).card
noncomputable def n3 (D : KerD45Data) : ℕ := (Finset.univ.filter fun i : Idx => 3 ≤ D.k i).card
noncomputable def nt (D : KerD45Data) : ℕ := ∑ i : Idx, (D.k i - 3)
noncomputable def a0 (D : KerD45Data) : ℕ := (D.Az.filter fun i : Idx => D.k i = 0).card
noncomputable def a1 (D : KerD45Data) : ℕ := (D.Az.filter fun i : Idx => D.k i = 1).card
noncomputable def a2 (D : KerD45Data) : ℕ := (D.Az.filter fun i : Idx => D.k i = 2).card
noncomputable def a3 (D : KerD45Data) : ℕ := (D.Az.filter fun i : Idx => 3 ≤ D.k i).card

attribute [irreducible] n0 n1 n2 n3 nt a0 a1 a2 a3

end KerD45Data
end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
