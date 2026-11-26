import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart5
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

lemma resOrdU0_sum :
    D.n1 + 11 * D.n2 + 29 * D.n3 + 18 * D.nt = ∑ i : Idx, resOrdU0 (D.k i) := by
  have hgen : ∀ S : Finset Idx,
      (S.filter fun i => D.k i = 1).card + 11 * (S.filter fun i => D.k i = 2).card +
      29 * (S.filter fun i => 3 ≤ D.k i).card + 18 * ∑ i ∈ S, (D.k i - 3) = ∑ i ∈ S, resOrdU0 (D.k i) := by
    intro S
    have hrew : (S.filter fun i => D.k i = 1).card + 11 * (S.filter fun i => D.k i = 2).card +
        29 * (S.filter fun i => 3 ≤ D.k i).card + 18 * ∑ i ∈ S, (D.k i - 3) =
        ∑ i ∈ S, ((if D.k i = 1 then 1 else 0) + (if D.k i = 2 then 11 else 0) +
          (if 3 ≤ D.k i then 29 else 0) + 18 * (D.k i - 3)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]; ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _; unfold resOrdU0; split_ifs <;> omega
  unfold n1 n2 n3 nt; exact hgen Finset.univ

lemma resOrdU0_le_natDegree : D.n1 + 11 * D.n2 + 29 * D.n3 + 18 * D.nt ≤ D.ResY.natDegree := by
  rw [D.resOrdU0_sum]
  exact sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    D.ResY D.ResY_ne_zero _ (fun i _ => D.pow_dvd_ResY_U0 i)

/-- **Universal `baseT4Rows` satisfaction lemma:**
Any vector `x : Fin nv → ℚ` whose coordinates `0..8` are `(n0, n1, n2, n3, nt, a0, a1, a2, a3) / N`
and whose coordinate `ic` is `W_F / wY` satisfies ALL rows of `baseT4Rows` whenever
`c ∈ [cLo, cHi]` and `G_z / N ∈ [loG, hiG]`! -/
theorem baseT4Rows_sat {nv ic : ℕ} (hic : 9 ≤ ic) (hic_lt : ic < nv)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (x : Fin nv → ℚ)
    (hx0 : x ⟨0, by omega⟩ = (D.n0 : ℚ) / (N : ℚ))
    (hx1 : x ⟨1, by omega⟩ = (D.n1 : ℚ) / (N : ℚ))
    (hx2 : x ⟨2, by omega⟩ = (D.n2 : ℚ) / (N : ℚ))
    (hx3 : x ⟨3, by omega⟩ = (D.n3 : ℚ) / (N : ℚ))
    (hx4 : x ⟨4, by omega⟩ = (D.nt : ℚ) / (N : ℚ))
    (hx5 : x ⟨5, by omega⟩ = (D.a0 : ℚ) / (N : ℚ))
    (hx6 : x ⟨6, by omega⟩ = (D.a1 : ℚ) / (N : ℚ))
    (hx7 : x ⟨7, by omega⟩ = (D.a2 : ℚ) / (N : ℚ))
    (hx8 : x ⟨8, by omega⟩ = (D.a3 : ℚ) / (N : ℚ))
    (hxic : x ⟨ic, hic_lt⟩ = (D.W_F : ℚ) / (wY : ℚ))
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ))
    (hcHi : (D.W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (hloG : (loGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≥ (loGNum * N : ℤ))
    (hhiG : hiGNum < hiGDen → (hiGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≤ (hiGNum * N : ℤ)) :
    let (ubB, eqB) := baseT4Rows ic cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    (∀ r ∈ ubB, RowSatLe x r) ∧ (∀ r ∈ eqB, RowSatEq x r) :=
  baseT4Rows_sat_aux hic hic_lt D.n0 D.n1 D.n2 D.n3 D.nt D.a0 D.a1 D.a2 D.a3 D.W_F
    D.hWF_lo (by rw [D.a_sum_eq_card]; exact D.hAz_card) D.a_le_n D.a1_3a2_5a3_le D.n3_2nt_le D.n_sum_eq_N
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD x
    hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hxic hcLo hcHi hloG hhiG

/-! ### Part 6: Coefficient Matrix `M`, `T4ABranch.det`, and `T4ABranch.p0Zero` -/

/-- The `3 × 3` matrix `M = [[P_0, C_0, B_0], [P_1, C_1, B_1], [P_2, C_2, B_2]]` over `Fld[T]`. -/
noncomputable def coeffMat : Matrix (Fin 3) (Fin 3) Fld[X] :=
  Matrix.of fun j c => match c.val with | 0 => D.Pj j | 1 => D.Cj j | _ => D.Bj j

noncomputable def detM : Fld[X] := D.coeffMat.det

end KerD45Data
end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
