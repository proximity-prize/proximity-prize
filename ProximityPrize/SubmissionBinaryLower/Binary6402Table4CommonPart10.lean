import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart9
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

theorem detMass6402 (hdet : D.detM ≠ 0) : 2 * (2 * D.n2 + 5 * D.n3 + 3 * D.nt) ≤ 3 * D.W_F - 8 * wY + 1 := by
    have hsum : 2 * D.n2 + 5 * D.n3 + 3 * D.nt = ∑ i : Idx, detOrd (D.k i) := by
      have hgen : ∀ S : Finset Idx,
          2 * (S.filter fun i => D.k i = 2).card + 5 * (S.filter fun i => 3 ≤ D.k i).card +
          3 * ∑ i ∈ S, (D.k i - 3) = ∑ i ∈ S, detOrd (D.k i) := by
        clear * - D
        intro S
        have hrew : 2 * (S.filter fun i => D.k i = 2).card + 5 * (S.filter fun i => 3 ≤ D.k i).card +
            3 * ∑ i ∈ S, (D.k i - 3) =
            ∑ i ∈ S, ((if D.k i = 2 then 2 else 0) + (if 3 ≤ D.k i then 5 else 0) + 3 * (D.k i - 3)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]; ring
        rw [hrew]; apply Finset.sum_congr rfl; intro i _; unfold detOrd; split_ifs <;> omega
      unfold n2 n3 nt; exact hgen Finset.univ
    have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i : Idx => BinaryIRSProfile.domain i ^ 2)
      domain_sq_injective D.detM hdet _ (fun i _ => D.pow_dvd_detM i)
    rw [← hsum] at hle
    have hdeg := D.two_mul_natDegree_detM_le
    clear * - hle hdeg
    omega

theorem detResRow6402Numeric (n0 n1 n2 n3 nt a0 a1 a2 a3 W_F : ℕ) (hwf : 5*wY≤W_F+1) (hResB : n1 + 11 * n2 + 29 * n3 + 18 * nt ≤ 9 * W_F - 25 * wY + 5) : RowSatLe (rawDetCoordinates n0 n1 n2 n3 nt a0 a1 a2 a3 W_F) (mkStat [(1,cI 1),(2,cI 11),(3,cI 29),(4,cI 18),(9,cH (-9))] (-50)) := by
  have hc_nn : (0 : ℚ) ≤ (W_F : ℚ) / (wY : ℚ) := by positivity
  have hN_eq : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  rw [rowSatLe_mkStat_iff]
  simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    show (1 : ℕ) < 10 by decide, show (2 : ℕ) < 10 by decide, show (3 : ℕ) < 10 by decide,
    show (4 : ℕ) < 10 by decide, show (9 : ℕ) < 10 by decide, ↓reduceDIte, ↓reduceIte, rawDetCoordinates, cI_mul_div_N, cH_mul_c_eq]
  have hResQ : (n1 : ℚ) + 11 * (n2 : ℚ) + 29 * (n3 : ℚ) + 18 * (nt : ℚ) ≤
      9 * (W_F : ℚ) - 25 * (wY : ℚ) + 5 := by
    have h25 : 25 * wY ≤ 9 * W_F := by have := hwf; have := (by decide : 0<wY); omega
    have hZ : ((n1 + 11 * n2 + 29 * n3 + 18 * nt : ℕ) : ℤ) ≤ 9 * (W_F : ℤ) - 25 * (wY : ℤ) + 5 := by clear * - hResB h25; omega
    exact_mod_cast hZ
  push_cast; rw [hN_eq]; linarith only [hResQ,hc_nn]

end KerD45Data
end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
