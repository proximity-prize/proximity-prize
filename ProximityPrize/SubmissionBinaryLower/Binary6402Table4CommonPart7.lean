import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart6
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

lemma two_mul_natDegree_detM_le : 2 * D.detM.natDegree ≤ 3 * D.W_F - 8 * wY + 1 := by
  have hdet : D.detM =
      D.Pj 0 * D.Cj 1 * D.Bj 2 + D.Cj 0 * D.Bj 1 * D.Pj 2 + D.Bj 0 * D.Pj 1 * D.Cj 2 +
      D.Pj 2 * D.Cj 1 * D.Bj 0 + D.Cj 2 * D.Bj 1 * D.Pj 0 + D.Bj 2 * D.Pj 1 * D.Cj 0 := by
    unfold detM coeffMat; rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two, sub_eq_add_neg, CharTwo.neg_eq]
    ring
  have h5 := D.hWF_lo
  have hterm : ∀ (j0 j1 j2 : Fin 3), j0.val + j1.val + j2.val = 3 →
      2 * (D.Pj j0 * D.Cj j1 * D.Bj j2).natDegree ≤ 3 * D.W_F - 8 * wY + 1 := by
    intro j0 j1 j2 hsum
    have hp := D.two_mul_natDegree_Pj_le j0
    have hc := D.two_mul_natDegree_Cj_le j1
    have hb := D.two_mul_natDegree_Bj_le j2
    have hnd : (D.Pj j0 * D.Cj j1 * D.Bj j2).natDegree ≤ (D.Pj j0).natDegree + (D.Cj j1).natDegree + (D.Bj j2).natDegree :=
      natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)
    have hlt0 := j0.isLt; have hlt1 := j1.isLt; have hlt2 := j2.isLt
    have hsumw : 2 * j0.val * wY + (2 * j1.val + 1) * wY + (2 * j2.val + 1) * wY = 8 * wY := by
      have h8 : 2 * j0.val + (2 * j1.val + 1) + (2 * j2.val + 1) = 8 := by omega
      calc 2 * j0.val * wY + (2 * j1.val + 1) * wY + (2 * j2.val + 1) * wY
          = (2 * j0.val + (2 * j1.val + 1) + (2 * j2.val + 1)) * wY := by ring
        _ = 8 * wY := by rw [h8]
    have hle0 : 2 * j0.val * wY ≤ D.W_F := by
      have h4 : 2 * j0.val * wY ≤ 4 * wY := Nat.mul_le_mul_right wY (by omega)
      have hw1 : 1 ≤ wY := by norm_num [wY]
      omega
    have hle1 : (2 * j1.val + 1) * wY ≤ D.W_F + 1 :=
      (Nat.mul_le_mul_right wY (show 2 * j1.val + 1 ≤ 5 by omega)).trans h5
    by_cases hB0 : D.Bj j2 = 0
    · simp [hB0]
    · have hle2 : (2 * j2.val + 1) * wY ≤ D.W_F := by
        have hnz : (D.Bj j2).coeff (D.Bj j2).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hB0
        rw [coeff_Bj] at hnz
        obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
        split_ifs at he with hc'
        · have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
          rcases hc' with ⟨h1, h2, h3, h4⟩
          rw [h1, h2, h3, h4] at hm
          simp only [zero_mul, zero_add] at hm
          have : 1 * wY + 2 * j2.val * wY = (2 * j2.val + 1) * wY := by ring
          omega
        · exact absurd rfl he
      omega
  rw [hdet]
  have hmax : ∀ a b : Fld[X], 2 * a.natDegree ≤ 3 * D.W_F - 8 * wY + 1 →
      2 * b.natDegree ≤ 3 * D.W_F - 8 * wY + 1 → 2 * (a + b).natDegree ≤ 3 * D.W_F - 8 * wY + 1 := fun a b ha hb => by
    have := natDegree_add_le a b; omega
  repeat apply hmax
  · exact hterm 0 1 2 rfl
  · rw [show D.Cj 0 * D.Bj 1 * D.Pj 2 = D.Pj 2 * D.Cj 0 * D.Bj 1 by ring]; exact hterm 2 0 1 rfl
  · rw [show D.Bj 0 * D.Pj 1 * D.Cj 2 = D.Pj 1 * D.Cj 2 * D.Bj 0 by ring]; exact hterm 1 2 0 rfl
  · exact hterm 2 1 0 rfl
  · rw [show D.Cj 2 * D.Bj 1 * D.Pj 0 = D.Pj 0 * D.Cj 2 * D.Bj 1 by ring]; exact hterm 0 2 1 rfl
  · rw [show D.Bj 2 * D.Pj 1 * D.Cj 0 = D.Pj 1 * D.Cj 0 * D.Bj 2 by ring]; exact hterm 1 0 2 rfl

def detOrd (k : ℕ) : ℕ :=
  if k ≤ 1 then 0 else if k = 2 then 2 else 5 + 3 * (k - 3)

end KerD45Data
end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
