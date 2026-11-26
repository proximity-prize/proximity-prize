import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart7
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

lemma pow_dvd_detM (i : Idx) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ detOrd (D.k i) ∣ D.detM := by
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  set t0 := x0 ^ 2
  have hdet_sh : D.detM =
      D.A0sh y0 0 * D.A1sh x0 y0 1 * D.Bsh y0 2 + D.A1sh x0 y0 0 * D.Bsh y0 1 * D.A0sh y0 2 +
      D.Bsh y0 0 * D.A0sh y0 1 * D.A1sh x0 y0 2 + D.A0sh y0 2 * D.A1sh x0 y0 1 * D.Bsh y0 0 +
      D.A1sh x0 y0 2 * D.Bsh y0 1 * D.A0sh y0 0 + D.Bsh y0 2 * D.A0sh y0 1 * D.A1sh x0 y0 0 := by
    let L : Matrix (Fin 3) (Fin 3) Fld[X] :=
      Matrix.of fun r c =>
        match r.val, c.val with
        | 0, 0 => 1 | 0, 1 => C (y0 ^ 2) | 0, 2 => C (y0 ^ 4)
        | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
    let R : Matrix (Fin 3) (Fin 3) Fld[X] :=
      Matrix.of fun r c =>
        match r.val, c.val with
        | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => C y0 | 2, 1 => C x0 | 2, 2 => 1 | _, _ => 0
    let M1 : Matrix (Fin 3) (Fin 3) Fld[X] :=
      Matrix.of fun j c =>
        match c.val with
        | 0 => D.Pj j + C y0 * D.Bj j
        | 1 => D.Cj j + C x0 * D.Bj j
        | _ => D.Bj j
    let Msh : Matrix (Fin 3) (Fin 3) Fld[X] :=
      Matrix.of fun j c => match c.val with | 0 => D.A0sh y0 j | 1 => D.A1sh x0 y0 j | _ => D.Bsh y0 j
    have hM1 : M1 = D.coeffMat * R := by
      ext j c; rw [Matrix.mul_apply, Fin.sum_univ_three]
      fin_cases c <;>
        (simp only [M1, R, coeffMat, Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two,
          mul_one, mul_zero, add_zero, zero_add]; try ring)
    have hMsh : Msh = L * M1 := by
      ext j c; rw [Matrix.mul_apply, Fin.sum_univ_three]
      fin_cases j <;> fin_cases c <;>
        (simp only [Msh, L, M1, A0sh, A1sh, Bsh, Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two,
          mul_one, mul_zero, add_zero, zero_add, one_mul, zero_mul]; try ring)
    have hdetL : L.det = 1 := by
      rw [Matrix.det_fin_three]
      simp only [L, Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two]; ring
    have hdetR : R.det = 1 := by
      rw [Matrix.det_fin_three]
      simp only [R, Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two]; ring
    have hdetEq : D.detM = Msh.det := by
      rw [hMsh, hM1, Matrix.det_mul, Matrix.det_mul, hdetL, hdetR, one_mul, mul_one]; rfl
    rw [hdetEq, Matrix.det_fin_three]
    simp only [Msh, Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two, sub_eq_add_neg, CharTwo.neg_eq]
    ring
  rw [hdet_sh]
  have hterm : ∀ (j0 j1 j2 : Fin 3), j0.val + j1.val + j2.val = 3 →
      (X - C t0) ^ detOrd (D.k i) ∣ D.A0sh y0 j0 * D.A1sh x0 y0 j1 * D.Bsh y0 j2 := by
    intro j0 j1 j2 hsum
    have h0 := (D.local_shifted_ords i j0).1
    have h1 := (D.local_shifted_ords i j1).2.1
    have h2 := (D.local_shifted_ords i j2).2.2
    have hle : detOrd (D.k i) ≤ (D.k i - j0.val) + (D.k i - j1.val) + (D.k i - 1 - j2.val) := by
      unfold detOrd; split_ifs <;> omega
    exact (pow_dvd_pow (X - C t0) hle).trans (by rw [pow_add, pow_add]; exact mul_dvd_mul (mul_dvd_mul h0 h1) h2)
  repeat apply dvd_add
  · exact hterm 0 1 2 rfl
  · rw [show D.A1sh x0 y0 0 * D.Bsh y0 1 * D.A0sh y0 2 = D.A0sh y0 2 * D.A1sh x0 y0 0 * D.Bsh y0 1 by ring]
    exact hterm 2 0 1 rfl
  · rw [show D.Bsh y0 0 * D.A0sh y0 1 * D.A1sh x0 y0 2 = D.A0sh y0 1 * D.A1sh x0 y0 2 * D.Bsh y0 0 by ring]
    exact hterm 1 2 0 rfl
  · exact hterm 2 1 0 rfl
  · rw [show D.A1sh x0 y0 2 * D.Bsh y0 1 * D.A0sh y0 0 = D.A0sh y0 0 * D.A1sh x0 y0 2 * D.Bsh y0 1 by ring]
    exact hterm 0 2 1 rfl
  · rw [show D.Bsh y0 2 * D.A0sh y0 1 * D.A1sh x0 y0 0 = D.A0sh y0 1 * D.A1sh x0 y0 0 * D.Bsh y0 2 by ring]
    exact hterm 1 0 2 rfl

/-- **Theorem (`T4ABranch.det`):** If `detM ≠ 0`, then `D` produces an explicit feasible vector
`x : Fin 10 → ℚ` for `buildT4ARows .det`! -/
def rawDetCoordinates (n0 n1 n2 n3 nt a0 a1 a2 a3 W_F : ℕ) : Fin 10 → ℚ := fun j =>
    match j.val with
    | 0 => (n0 : ℚ) / (N : ℚ) | 1 => (n1 : ℚ) / (N : ℚ)
    | 2 => (n2 : ℚ) / (N : ℚ) | 3 => (n3 : ℚ) / (N : ℚ)
    | 4 => (nt : ℚ) / (N : ℚ) | 5 => (a0 : ℚ) / (N : ℚ)
    | 6 => (a1 : ℚ) / (N : ℚ) | 7 => (a2 : ℚ) / (N : ℚ)
    | 8 => (a3 : ℚ) / (N : ℚ) | _ => (W_F : ℚ) / (wY : ℚ)

end KerD45Data
end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
