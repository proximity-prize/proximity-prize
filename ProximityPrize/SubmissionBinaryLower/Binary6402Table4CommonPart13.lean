import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart12
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

theorem table4_det_sat (hdet : D.detM ≠ 0)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ))
    (hcHi : (D.W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (hloG : (loGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≥ (loGNum * N : ℤ))
    (hhiG : hiGNum < hiGDen → (hiGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≤ (hiGNum * N : ℤ)) :
    let rows := buildT4ARows .det cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    ∃ x : Fin (t4aNumVars .det) → ℚ,
      (∀ j, 0 ≤ x j) ∧
      x ⟨0, by decide⟩ = (D.n0 : ℚ) / (N : ℚ) ∧ x ⟨1, by decide⟩ = (D.n1 : ℚ) / (N : ℚ) ∧
      x ⟨2, by decide⟩ = (D.n2 : ℚ) / (N : ℚ) ∧ x ⟨3, by decide⟩ = (D.n3 : ℚ) / (N : ℚ) ∧
      x ⟨4, by decide⟩ = (D.nt : ℚ) / (N : ℚ) ∧ x ⟨9, by decide⟩ = (D.W_F : ℚ) / (wY : ℚ) ∧
      (∀ r ∈ rows.1.toList, RowValid (t4aNumVars .det) r ∧ RowSatLe x r) ∧
      (∀ r ∈ rows.2.toList, RowValid (t4aNumVars .det) r ∧ RowSatEq x r) := by
  let x := D.detCoordinates6402
  refine ⟨x, fun j => by dsimp only [x,detCoordinates6402,rawDetCoordinates]; split <;> positivity, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only [t4aNumVars]
  have hBV := baseT4Rows_valid (nv := 10) (ic := 9) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD
  have hBS := D.baseT4Rows_sat (nv := 10) (ic := 9) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD x
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcLo hcHi hloG hhiG
  have hc_nn : (0 : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ) := by positivity
  have hN_eq : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  constructor
  · intro r hr
    simp only [buildT4ARows, t4aNumVars, t4aStaticRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact ⟨hBV.1 r hr, hBS.1 r hr⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        exact D.detResRow6402
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
        exact D.detDegreeRow6402 hdet
  · intro r hr
    simp only [buildT4ARows, t4aNumVars, t4aStaticRows, List.toList_toArray, List.append_nil] at hr
    exact ⟨hBV.2 r hr, hBS.2 r hr⟩

end KerD45Data
end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
