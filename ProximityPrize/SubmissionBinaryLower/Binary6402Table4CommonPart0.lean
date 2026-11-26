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

/-! ### Part 1: `SparseRow`, `baseT4Rows`, and `W_F ↔ c` Bridge Helpers -/

/-- Exact dot product of a `SparseRow` against `x : Fin nv → ℚ`, matching `checkT4Bucket_sound`. -/
def evalRow {nv : ℕ} (x : Fin nv → ℚ) (r : SparseRow) : ℚ :=
  (r.entries.map fun e => if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum

/-- Inequality satisfaction predicate matching `checkT4Bucket_sound`'s `hub_sat`. -/
def RowSatLe {nv : ℕ} (x : Fin nv → ℚ) (r : SparseRow) : Prop :=
  evalRow x r ≤ (BASE_DEN : ℚ) * (r.rhsNum : ℚ) / (r.rhsDen : ℚ)

/-- Equality satisfaction predicate matching `checkT4Bucket_sound`'s `heq_sat`. -/
def RowSatEq {nv : ℕ} (x : Fin nv → ℚ) (r : SparseRow) : Prop :=
  evalRow x r = (BASE_DEN : ℚ) * (r.rhsNum : ℚ) / (r.rhsDen : ℚ)

/-- Well-formedness predicate matching `checkT4Bucket_sound`'s `hubD`/`heqD` and `hubE`/`heqE`. -/
def RowValid (nv : ℕ) (r : SparseRow) : Prop :=
  0 < r.rhsDen ∧ ∀ e ∈ r.entries, e.1 < nv

lemma base_den_pos : (0 : ℤ) < BASE_DEN := by norm_num [BASE_DEN, N]

lemma base_den_ne_zeroQ : (BASE_DEN : ℚ) ≠ 0 := by norm_num [BASE_DEN, N]

lemma N_posQ : (0 : ℚ) < (N : ℚ) := by norm_num [N]

lemma wY_posQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]

lemma two_mul_wY_add_two : 2 * wY + 2 = N := by norm_num [wY, N]

lemma evalRow_mkStat {nv : ℕ} (x : Fin nv → ℚ) (entries : List (Nat × Int)) (num4 : ℤ) (eps : Bool) :
    evalRow x (mkStat entries num4 eps) =
      (entries.map fun e => if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum := rfl

lemma rowSatLe_mkStat_iff {nv : ℕ} (x : Fin nv → ℚ) (entries : List (Nat × Int))
    (num4 : ℤ) (eps : Bool) :
    RowSatLe x (mkStat entries num4 eps) ↔
      (entries.map fun e => if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum ≤
        (num4 : ℚ) * (N : ℚ) + if eps then 120 else 0 := by
  unfold RowSatLe evalRow mkStat
  have hne : (BASE_DEN : ℚ) ≠ 0 := base_den_ne_zeroQ
  rw [mul_div_cancel_left₀ _ hne]
  cases eps <;> simp

lemma rowSatEq_mkEq_iff {nv : ℕ} (x : Fin nv → ℚ) (entries : List (Nat × Int)) (num4 : ℤ) :
    RowSatEq x (mkEq entries num4) ↔
      (entries.map fun e => if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum =
        (num4 : ℚ) * (N : ℚ) := by
  unfold RowSatEq evalRow mkEq
  have hne : (BASE_DEN : ℚ) ≠ 0 := base_den_ne_zeroQ
  rw [mul_div_cancel_left₀ _ hne]
  simp

lemma rowValid_mkStat {nv : ℕ} (entries : List (Nat × Int)) (num4 : ℤ) (eps : Bool)
    (h : ∀ e ∈ entries, e.1 < nv) : RowValid nv (mkStat entries num4 eps) :=
  ⟨base_den_pos, h⟩

lemma rowValid_mkEq {nv : ℕ} (entries : List (Nat × Int)) (num4 : ℤ)
    (h : ∀ e ∈ entries, e.1 < nv) : RowValid nv (mkEq entries num4) :=
  ⟨base_den_pos, h⟩

lemma cI_mul_div_N (k : ℤ) (v : ℚ) : (cI k : ℚ) * (v / (N : ℚ)) = 4 * (k : ℚ) * v := by
  unfold cI BASE_DEN; push_cast
  have hN : (N : ℚ) ≠ 0 := N_posQ.ne'
  field_simp [hN]

lemma cH_mul_div_N (k : ℤ) (v : ℚ) : (cH k : ℚ) * (v / (N : ℚ)) = 2 * (k : ℚ) * v := by
  unfold cH; push_cast
  have hN : (N : ℚ) ≠ 0 := N_posQ.ne'
  field_simp [hN]

lemma cQ_mul_div_N (k : ℤ) (v : ℚ) : (cQ k : ℚ) * (v / (N : ℚ)) = (k : ℚ) * v := by
  unfold cQ; push_cast
  have hN : (N : ℚ) ≠ 0 := N_posQ.ne'
  field_simp [hN]

lemma cW_mul_div_wY (k : ℤ) (W : ℚ) : (cW k : ℚ) * (W / (wY : ℚ)) = 4 * (k : ℚ) * W := by
  unfold cW; push_cast
  have hw : (wY : ℚ) ≠ 0 := wY_posQ.ne'
  field_simp [hw]

lemma cI_mul_c_eq (k : ℤ) (W : ℚ) :
    (cI k : ℚ) * (W / (wY : ℚ)) = 8 * (k : ℚ) * W + 8 * (k : ℚ) * (W / (wY : ℚ)) := by
  unfold cI BASE_DEN
  have hN : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  have hw : (wY : ℚ) ≠ 0 := wY_posQ.ne'
  push_cast; rw [hN]; field_simp [hw]; ring

lemma cH_mul_c_eq (k : ℤ) (W : ℚ) :
    (cH k : ℚ) * (W / (wY : ℚ)) = 4 * (k : ℚ) * W + 4 * (k : ℚ) * (W / (wY : ℚ)) := by
  unfold cH
  have hN : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  have hw : (wY : ℚ) ≠ 0 := wY_posQ.ne'
  push_cast; rw [hN]; field_simp [hw]; ring

lemma cQ_mul_c_eq (k : ℤ) (W : ℚ) :
    (cQ k : ℚ) * (W / (wY : ℚ)) = 2 * (k : ℚ) * W + 2 * (k : ℚ) * (W / (wY : ℚ)) := by
  unfold cQ
  have hN : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  have hw : (wY : ℚ) ≠ 0 := wY_posQ.ne'
  push_cast; rw [hN]; field_simp [hw]; try ring

/-- Convert list-level `RowValid` / `RowSatLe` / `RowSatEq` to the `Array` hypotheses of
`B6402IntFarkas.checkT4Bucket_sound`. -/
lemma array_row_props_of_list {nv : ℕ} {x : Fin nv → ℚ} {ubL eqL : List SparseRow}
    (hubV : ∀ r ∈ ubL, RowValid nv r) (heqV : ∀ r ∈ eqL, RowValid nv r)
    (hubS : ∀ r ∈ ubL, RowSatLe x r) (heqS : ∀ r ∈ eqL, RowSatEq x r) :
    (∀ i (hi : i < ubL.toArray.size), 0 < (ubL.toArray[i]).rhsDen) ∧
    (∀ i (hi : i < eqL.toArray.size), 0 < (eqL.toArray[i]).rhsDen) ∧
    (∀ i (hi : i < ubL.toArray.size), ∀ e ∈ (ubL.toArray[i]).entries, e.1 < nv) ∧
    (∀ i (hi : i < eqL.toArray.size), ∀ e ∈ (eqL.toArray[i]).entries, e.1 < nv) ∧
    (∀ i (hi : i < ubL.toArray.size),
      ((ubL.toArray[i]).entries.map fun e => if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum ≤
        (BASE_DEN : ℚ) * ((ubL.toArray[i]).rhsNum : ℚ) / ((ubL.toArray[i]).rhsDen : ℚ)) ∧
    (∀ i (hi : i < eqL.toArray.size),
      ((eqL.toArray[i]).entries.map fun e => if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum =
        (BASE_DEN : ℚ) * ((eqL.toArray[i]).rhsNum : ℚ) / ((eqL.toArray[i]).rhsDen : ℚ)) := by
  have hmem : ∀ {L : List SparseRow} {i : ℕ} (hi : i < L.toArray.size), L.toArray[i] ∈ L := by
    intro L i hi
    simpa [Array.mem_toList_iff] using Array.getElem_mem hi
  refine ⟨fun i hi => (hubV _ (hmem hi)).1,
          fun i hi => (heqV _ (hmem hi)).1,
          fun i hi => (hubV _ (hmem hi)).2,
          fun i hi => (heqV _ (hmem hi)).2,
          fun i hi => hubS _ (hmem hi),
          fun i hi => heqS _ (hmem hi)⟩

/-- Validity of `baseT4Rows`. -/
lemma baseT4Rows_valid {nv ic : ℕ} (hic : 9 ≤ ic) (hic_lt : ic < nv)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen) :
    let (ubB, eqB) := baseT4Rows ic cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    (∀ r ∈ ubB, RowValid nv r) ∧ (∀ r ∈ eqB, RowValid nv r) := by
  unfold baseT4Rows
  dsimp only
  have hNpos : (0 : ℤ) < (N : ℤ) := by norm_num [N]
  have hloD : (0 : ℤ) < (N : ℤ) * (loGDen : ℤ) := mul_pos hNpos (by exact_mod_cast hloGD)
  have hhiD : (0 : ℤ) < (N : ℤ) * (hiGDen : ℤ) := mul_pos hNpos (by exact_mod_cast hhiGD)
  constructor
  · intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hr) | hr
    · exact rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega)
    · exact rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega)
    · exact rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega)
    · exact rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl <;> omega)
    · exact ⟨base_den_pos, by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega⟩
    · exact ⟨by dsimp; exact_mod_cast hcLoD, by intro e he; simp at he; rcases he with rfl; omega⟩
    · exact ⟨by dsimp; exact_mod_cast hcHiD, by intro e he; simp at he; rcases he with rfl; omega⟩
    · exact ⟨base_den_pos, by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega⟩
    · exact ⟨base_den_pos, by intro e he; simp at he; rcases he with rfl | rfl | rfl <;> omega⟩
    · split_ifs at hr with h
      · simp at hr; subst hr
        exact ⟨hloD, by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega⟩
      · simp at hr
    · split_ifs at hr with h
      · simp at hr; subst hr
        exact ⟨hhiD, by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega⟩
      · simp at hr
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact rowValid_mkEq _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega)

theorem baseT4Rows_sat_aux {nv ic : ℕ} (hic : 9 ≤ ic) (hic_lt : ic < nv)
    (n0 n1 n2 n3 nt a0 a1 a2 a3 W_F : ℕ)
    (hWF_lo : 5 * wY ≤ W_F + 1)
    (hA_nat : A ≤ a0 + a1 + a2 + a3)
    (ha_le : a0 ≤ n0 ∧ a1 ≤ n1 ∧ a2 ≤ n2 ∧ a3 ≤ n3)
    (ha135 : a1 + 3 * a2 + 5 * a3 ≤ W_F - wY + 1)
    (hn32 : n3 + 2 * nt ≤ W_F + 1 - 5 * wY)
    (hnsum : n0 + n1 + n2 + n3 = N)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (_hcLoD : 0 < cLoDen) (_hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (x : Fin nv → ℚ)
    (hx0 : x ⟨0, by omega⟩ = (n0 : ℚ) / (N : ℚ))
    (hx1 : x ⟨1, by omega⟩ = (n1 : ℚ) / (N : ℚ))
    (hx2 : x ⟨2, by omega⟩ = (n2 : ℚ) / (N : ℚ))
    (hx3 : x ⟨3, by omega⟩ = (n3 : ℚ) / (N : ℚ))
    (hx4 : x ⟨4, by omega⟩ = (nt : ℚ) / (N : ℚ))
    (hx5 : x ⟨5, by omega⟩ = (a0 : ℚ) / (N : ℚ))
    (hx6 : x ⟨6, by omega⟩ = (a1 : ℚ) / (N : ℚ))
    (hx7 : x ⟨7, by omega⟩ = (a2 : ℚ) / (N : ℚ))
    (hx8 : x ⟨8, by omega⟩ = (a3 : ℚ) / (N : ℚ))
    (hxic : x ⟨ic, hic_lt⟩ = (W_F : ℚ) / (wY : ℚ))
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (W_F : ℚ) / (wY : ℚ))
    (hcHi : (W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (hloG : (loGDen : ℤ) * ((W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((a1 + 3 * a2 + 5 * a3 : ℕ) : ℤ) + (a0 : ℤ)) ≥ (loGNum * N : ℤ))
    (hhiG : hiGNum < hiGDen → (hiGDen : ℤ) * ((W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((a1 + 3 * a2 + 5 * a3 : ℕ) : ℤ) + (a0 : ℤ)) ≤ (hiGNum * N : ℤ)) :
    let (ubB, eqB) := baseT4Rows ic cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    (∀ r ∈ ubB, RowSatLe x r) ∧ (∀ r ∈ eqB, RowSatEq x r) := by
  unfold baseT4Rows
  dsimp only
  have hBne : (BASE_DEN : ℚ) ≠ 0 := base_den_ne_zeroQ
  have hBpos : (0 : ℚ) < (BASE_DEN : ℚ) := by exact_mod_cast base_den_pos
  have hNpos : (0 : ℚ) < (N : ℚ) := N_posQ
  have hloGDQ : (0 : ℚ) < (loGDen : ℚ) := by exact_mod_cast hloGD
  have hhiGDQ : (0 : ℚ) < (hiGDen : ℚ) := by exact_mod_cast hhiGD
  have ⟨ha0, ha1, ha2, ha3⟩ := ha_le
  constructor
  · intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hr) | hr
    · rw [rowSatLe_mkStat_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (0 : ℕ) < nv by omega, show (5 : ℕ) < nv by omega, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte,
        hx0, hx5, cI_mul_div_N]
      have h : (a0 : ℚ) ≤ (n0 : ℚ) := by exact_mod_cast ha0
      push_cast; linarith only [h]
    · rw [rowSatLe_mkStat_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (1 : ℕ) < nv by omega, show (6 : ℕ) < nv by omega, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte,
        hx1, hx6, cI_mul_div_N]
      have h : (a1 : ℚ) ≤ (n1 : ℚ) := by exact_mod_cast ha1
      push_cast; linarith only [h]
    · rw [rowSatLe_mkStat_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (2 : ℕ) < nv by omega, show (7 : ℕ) < nv by omega, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte,
        hx2, hx7, cI_mul_div_N]
      have h : (a2 : ℚ) ≤ (n2 : ℚ) := by exact_mod_cast ha2
      push_cast; linarith only [h]
    · rw [rowSatLe_mkStat_iff]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (3 : ℕ) < nv by omega, show (8 : ℕ) < nv by omega, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte,
        hx3, hx8, cI_mul_div_N]
      have h : (a3 : ℚ) ≤ (n3 : ℚ) := by exact_mod_cast ha3
      push_cast; linarith only [h]
    · unfold RowSatLe
      rw [mul_div_cancel_left₀ _ hBne]
      simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (5 : ℕ) < nv by omega, show (6 : ℕ) < nv by omega, show (7 : ℕ) < nv by omega,
        show (8 : ℕ) < nv by omega, ↓reduceDIte, hx5, hx6, hx7, hx8, cI_mul_div_N]
      have hA : (A : ℚ) ≤ (a0 : ℚ) + (a1 : ℚ) + (a2 : ℚ) + (a3 : ℚ) := by exact_mod_cast hA_nat
      push_cast; linarith only [hA]
    · unfold RowSatLe
      simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hic_lt, ↓reduceDIte, hxic]
      rw [show (cI (-1) : ℚ) = -(BASE_DEN : ℚ) by unfold cI; push_cast; ring]
      push_cast
      have hmul := mul_le_mul_of_nonneg_left hcLo hBpos.le
      linarith only [hmul, show (BASE_DEN : ℚ) * -(cLoNum : ℚ) / (cLoDen : ℚ) = -((BASE_DEN : ℚ) * ((cLoNum : ℚ) / (cLoDen : ℚ))) by ring]
    · unfold RowSatLe
      simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hic_lt, ↓reduceDIte, hxic]
      rw [show (cI 1 : ℚ) = (BASE_DEN : ℚ) by unfold cI; push_cast; ring]
      push_cast
      have hmul := mul_le_mul_of_nonneg_left hcHi hBpos.le
      linarith only [hmul, show (BASE_DEN : ℚ) * (cHiNum : ℚ) / (cHiDen : ℚ) = (BASE_DEN : ℚ) * ((cHiNum : ℚ) / (cHiDen : ℚ)) by ring]
    · unfold RowSatLe
      rw [mul_div_cancel_left₀ _ hBne]
      simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (6 : ℕ) < nv by omega, show (7 : ℕ) < nv by omega, show (8 : ℕ) < nv by omega, hic_lt,
        ↓reduceDIte, hx6, hx7, hx8, hxic, cI_mul_div_N, cW_mul_div_wY]
      have h1 : (a1 : ℚ) + 3 * (a2 : ℚ) + 5 * (a3 : ℚ) ≤ (W_F : ℚ) - (wY : ℚ) + 1 := by
        have hw0 : 0 < wY := by norm_num [wY]
        have hw : wY ≤ W_F := by omega
        have hZ : ((a1 + 3 * a2 + 5 * a3 : ℕ) : ℤ) ≤ (W_F : ℤ) - (wY : ℤ) + 1 := by omega
        exact_mod_cast hZ
      push_cast; linarith only [h1]
    · unfold RowSatLe
      rw [mul_div_cancel_left₀ _ hBne]
      simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (3 : ℕ) < nv by omega, show (4 : ℕ) < nv by omega, hic_lt,
        ↓reduceDIte, hx3, hx4, hxic, cI_mul_div_N, cW_mul_div_wY]
      have h1 : (n3 : ℚ) + 2 * (nt : ℚ) ≤ (W_F : ℚ) - 5 * (wY : ℚ) + 1 := by
        have hZ : ((n3 + 2 * nt : ℕ) : ℤ) ≤ (W_F : ℤ) - 5 * (wY : ℤ) + 1 := by omega
        exact_mod_cast hZ
      push_cast; linarith only [h1]
    · split_ifs at hr with h
      · simp at hr; subst hr
        unfold RowSatLe
        simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (5 : ℕ) < nv by omega, show (6 : ℕ) < nv by omega, show (7 : ℕ) < nv by omega,
          show (8 : ℕ) < nv by omega, hic_lt, ↓reduceDIte, hx5, hx6, hx7, hx8, hxic, cI_mul_div_N, cW_mul_div_wY]
        have hG_Q : (loGNum : ℚ) * (N : ℚ) ≤ (loGDen : ℚ) *
            ((W_F : ℚ) - (wY : ℚ) + 1 - ((a1 : ℚ) + 3 * (a2 : ℚ) + 5 * (a3 : ℚ)) + (a0 : ℚ)) := by
          have hw1 : ((wY - 1 : ℕ) : ℤ) = (wY : ℤ) - 1 := by norm_num [wY]
          have hZ : (loGNum : ℤ) * (N : ℤ) ≤ (loGDen : ℤ) *
              ((W_F : ℤ) - (wY : ℤ) + 1 - ((a1 : ℤ) + 3 * (a2 : ℤ) + 5 * (a3 : ℤ)) + (a0 : ℤ)) := by
            rw [hw1] at hloG; push_cast at hloG ⊢; linarith
          exact_mod_cast hZ
        have hB_eq : (BASE_DEN : ℚ) = 4 * (N : ℚ) := by unfold BASE_DEN; push_cast; rfl
        rw [hB_eq, show (4 * (N : ℚ)) * (((-(wY : ℤ) + 1) * (loGDen : ℤ) - (loGNum : ℤ) * (N : ℤ) : ℤ) : ℚ) /
            (((N : ℤ) * (loGDen : ℤ) : ℤ) : ℚ) =
            4 * ((-(wY : ℚ) + 1) * (loGDen : ℚ) - (loGNum : ℚ) * (N : ℚ)) / (loGDen : ℚ) by
          push_cast; field_simp [hNpos.ne', hloGDQ.ne']]
        rw [le_div_iff₀ hloGDQ]
        have h4 := mul_le_mul_of_nonneg_left hG_Q (by norm_num : (0 : ℚ) ≤ 4)
        have hrew : (4 * (-1 : ℚ) * (a0 : ℚ) + (4 * (1 : ℚ) * (a1 : ℚ) + (4 * (3 : ℚ) * (a2 : ℚ) +
            (4 * (5 : ℚ) * (a3 : ℚ) + (4 * (-1 : ℚ) * (W_F : ℚ) + 0))))) * (loGDen : ℚ) =
            -(4 * ((loGDen : ℚ) * ((W_F : ℚ) - (wY : ℚ) + 1 -
              ((a1 : ℚ) + 3 * (a2 : ℚ) + 5 * (a3 : ℚ)) + (a0 : ℚ)))) +
              4 * (-(wY : ℚ) + 1) * (loGDen : ℚ) := by ring
        have hrhs : 4 * ((-(wY : ℚ) + 1) * (loGDen : ℚ) - (loGNum : ℚ) * (N : ℚ)) =
            -(4 * ((loGNum : ℚ) * (N : ℚ))) + 4 * (-(wY : ℚ) + 1) * (loGDen : ℚ) := by ring
        push_cast; linarith only [h4, hrew, hrhs]
      · simp at hr
    · split_ifs at hr with h
      · simp at hr; subst hr
        unfold RowSatLe
        simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (5 : ℕ) < nv by omega, show (6 : ℕ) < nv by omega, show (7 : ℕ) < nv by omega,
          show (8 : ℕ) < nv by omega, hic_lt, ↓reduceDIte, hx5, hx6, hx7, hx8, hxic, cI_mul_div_N, cW_mul_div_wY]
        have hG_Q : (hiGDen : ℚ) *
            ((W_F : ℚ) - (wY : ℚ) + 1 - ((a1 : ℚ) + 3 * (a2 : ℚ) + 5 * (a3 : ℚ)) + (a0 : ℚ)) ≤
            (hiGNum : ℚ) * (N : ℚ) := by
          have hw1 : ((wY - 1 : ℕ) : ℤ) = (wY : ℤ) - 1 := by norm_num [wY]
          have hZ : (hiGDen : ℤ) *
              ((W_F : ℤ) - (wY : ℤ) + 1 - ((a1 : ℤ) + 3 * (a2 : ℤ) + 5 * (a3 : ℤ)) + (a0 : ℤ)) ≤
              (hiGNum : ℤ) * (N : ℤ) := by
            have hhiG' := hhiG h
            rw [hw1] at hhiG'; push_cast at hhiG' ⊢; linarith
          exact_mod_cast hZ
        have hB_eq : (BASE_DEN : ℚ) = 4 * (N : ℚ) := by unfold BASE_DEN; push_cast; rfl
        rw [hB_eq, show (4 * (N : ℚ)) * ((((wY : ℤ) - 1) * (hiGDen : ℤ) + (hiGNum : ℤ) * (N : ℤ) : ℤ) : ℚ) /
            (((N : ℤ) * (hiGDen : ℤ) : ℤ) : ℚ) =
            4 * (((wY : ℚ) - 1) * (hiGDen : ℚ) + (hiGNum : ℚ) * (N : ℚ)) / (hiGDen : ℚ) by
          push_cast; field_simp [hNpos.ne', hhiGDQ.ne']]
        rw [le_div_iff₀ hhiGDQ]
        have h4 := mul_le_mul_of_nonneg_left hG_Q (by norm_num : (0 : ℚ) ≤ 4)
        have hrew : (4 * (1 : ℚ) * (a0 : ℚ) + (4 * (-1 : ℚ) * (a1 : ℚ) + (4 * (-3 : ℚ) * (a2 : ℚ) +
            (4 * (-5 : ℚ) * (a3 : ℚ) + (4 * (1 : ℚ) * (W_F : ℚ) + 0))))) * (hiGDen : ℚ) =
            4 * ((hiGDen : ℚ) * ((W_F : ℚ) - (wY : ℚ) + 1 -
              ((a1 : ℚ) + 3 * (a2 : ℚ) + 5 * (a3 : ℚ)) + (a0 : ℚ))) +
              4 * ((wY : ℚ) - 1) * (hiGDen : ℚ) := by ring
        have hrhs : 4 * (((wY : ℚ) - 1) * (hiGDen : ℚ) + (hiGNum : ℚ) * (N : ℚ)) =
            4 * ((hiGNum : ℚ) * (N : ℚ)) + 4 * ((wY : ℚ) - 1) * (hiGDen : ℚ) := by ring
        push_cast; linarith only [h4, hrew, hrhs]
      · simp at hr
  · intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [rowSatEq_mkEq_iff]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      show (0 : ℕ) < nv by omega, show (1 : ℕ) < nv by omega, show (2 : ℕ) < nv by omega,
      show (3 : ℕ) < nv by omega, ↓reduceDIte, hx0, hx1, hx2, hx3, cI_mul_div_N]
    have hN : (n0 : ℚ) + (n1 : ℚ) + (n2 : ℚ) + (n3 : ℚ) = (N : ℚ) := by exact_mod_cast hnsum
    push_cast; linarith only [hN]

/-! ### Part 2: Exact Char-2 Polynomial Helpers (`sqrtPoly`, `evenPart`, `oddPart`, `rootMultiplicity`) -/

/-- Exact square-root polynomial over the finite char-2 field `Fld`: `(sqrtPoly p)^2 = p(X^2)`. -/
noncomputable def sqrtPoly (p : Fld[X]) : Fld[X] :=
  p.map (frobEquiv Fld).symm.toRingHom

lemma sqrtPoly_sq (p : Fld[X]) : (sqrtPoly p) ^ 2 = p.comp (X ^ 2) := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb =>
      have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
      unfold sqrtPoly at ha hb ⊢
      rw [Polynomial.map_add, add_comp, ← ha, ← hb]
      calc (a.map _ + b.map _) ^ 2 = a.map _ ^ 2 + 2 * a.map _ * b.map _ + b.map _ ^ 2 := by ring
        _ = a.map _ ^ 2 + b.map _ ^ 2 := by rw [h2]; ring
  | monomial n c =>
      unfold sqrtPoly
      rw [map_monomial, monomial_comp, monomial_pow]
      change (monomial (n * 2)) (((frobEquiv Fld).symm c) ^ 2) = C c * (X ^ 2) ^ n
      rw [frobEquiv_symm_sq, ← pow_mul, mul_comm 2 n, C_mul_X_pow_eq_monomial]

lemma sqrtPoly_add (p q : Fld[X]) : sqrtPoly (p + q) = sqrtPoly p + sqrtPoly q := by
  unfold sqrtPoly; exact Polynomial.map_add _

lemma sqrtPoly_mul (p q : Fld[X]) : sqrtPoly (p * q) = sqrtPoly p * sqrtPoly q := by
  unfold sqrtPoly; exact Polynomial.map_mul _

lemma sqrtPoly_pow (p : Fld[X]) (n : ℕ) : sqrtPoly (p ^ n) = (sqrtPoly p) ^ n := by
  unfold sqrtPoly; exact Polynomial.map_pow _ _

lemma sqrtPoly_eq_zero_iff (p : Fld[X]) : sqrtPoly p = 0 ↔ p = 0 := by
  unfold sqrtPoly
  exact Polynomial.map_eq_zero_iff (frobEquiv Fld).symm.injective

lemma natDegree_sqrtPoly (p : Fld[X]) : (sqrtPoly p).natDegree = p.natDegree := by
  unfold sqrtPoly
  exact Polynomial.natDegree_map_eq_of_injective (frobEquiv Fld).symm.injective p

lemma eval_sqrtPoly_sq (p : Fld[X]) (x : Fld) : (sqrtPoly p).eval x ^ 2 = p.eval (x ^ 2) := by
  rw [← eval_pow, sqrtPoly_sq, eval_comp, eval_pow, eval_X]

lemma sqrtPoly_eval_eq_zero_iff (p : Fld[X]) (x : Fld) :
    (sqrtPoly p).eval x = 0 ↔ p.eval (x ^ 2) = 0 := by
  constructor
  · intro h; rw [← eval_sqrtPoly_sq, h]; ring
  · intro h; rw [← eval_sqrtPoly_sq] at h; exact sq_eq_zero_iff.mp h

lemma comp_X_sq_coeff_even {R : Type*} [CommRing R] (p : R[X]) (n : ℕ) :
    (p.comp (X ^ 2)).coeff (2 * n) = p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb => rw [add_comp, coeff_add, coeff_add, ha, hb]
  | monomial m c =>
      rw [monomial_comp, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial, coeff_monomial]
      by_cases h : m = n
      · subst h; simp
      · have h2 : 2 * m ≠ 2 * n := by omega
        simp [h, h2]

lemma comp_X_sq_coeff_odd {R : Type*} [CommRing R] (p : R[X]) (n : ℕ) :
    (p.comp (X ^ 2)).coeff (2 * n + 1) = 0 := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb => rw [add_comp, coeff_add, ha, hb, add_zero]
  | monomial m c =>
      rw [monomial_comp, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial]
      have h : 2 * m ≠ 2 * n + 1 := by omega
      simp [h]

lemma comp_X_sq_eq_zero_iff {R : Type*} [CommRing R] (p : R[X]) : p.comp (X ^ 2) = 0 ↔ p = 0 := by
  constructor
  · intro h; ext n
    have := congrArg (fun q : R[X] => q.coeff (2 * n)) h
    rw [comp_X_sq_coeff_even, coeff_zero] at this
    exact this
  · rintro rfl; simp

lemma natDegree_comp_X_sq {R : Type*} [CommRing R] [IsDomain R] (p : R[X]) :
    (p.comp (X ^ 2)).natDegree = 2 * p.natDegree := by
  rw [natDegree_comp, natDegree_X_pow, mul_comm]

lemma coeff_even_odd_pair {R : Type*} [CommRing R] (A B : R[X]) (n : ℕ) :
    (A.comp (X ^ 2) + X * B.comp (X ^ 2)).coeff n =
      if n % 2 = 0 then A.coeff (n / 2) else B.coeff (n / 2) := by
  rw [coeff_add]
  by_cases h : n % 2 = 0
  · simp only [h, ↓reduceIte]
    have hn : n = 2 * (n / 2) := by omega
    conv_lhs => rw [hn]
    rw [comp_X_sq_coeff_even]
    cases h0 : n / 2 with
    | zero => simp
    | succ m =>
        have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
        rw [h1, coeff_X_mul, comp_X_sq_coeff_odd, add_zero]
  · simp only [h, ↓reduceIte]
    have hn : n = 2 * (n / 2) + 1 := by omega
    conv_lhs => rw [hn]
    rw [comp_X_sq_coeff_odd, zero_add, coeff_X_mul, comp_X_sq_coeff_even]

lemma even_odd_pair_eq_zero_iff {R : Type*} [CommRing R] (A B : R[X]) :
    A.comp (X ^ 2) + X * B.comp (X ^ 2) = 0 ↔ A = 0 ∧ B = 0 := by
  constructor
  · intro h
    constructor <;> ext n
    · have := congrArg (fun q : R[X] => q.coeff (2 * n)) h
      rw [coeff_even_odd_pair, coeff_zero] at this
      have hm : (2 * n) % 2 = 0 := by omega
      have hd : (2 * n) / 2 = n := by omega
      simpa [hm, hd] using this
    · have := congrArg (fun q : R[X] => q.coeff (2 * n + 1)) h
      rw [coeff_even_odd_pair, coeff_zero] at this
      have hm : ¬ (2 * n + 1) % 2 = 0 := by omega
      have hd : (2 * n + 1) / 2 = n := by omega
      simpa [hm, hd] using this
  · rintro ⟨rfl, rfl⟩; simp

lemma two_mul_natDegree_le_even_odd {R : Type*} [CommRing R] (A B : R[X]) (hA : A ≠ 0) :
    2 * A.natDegree ≤ (A.comp (X ^ 2) + X * B.comp (X ^ 2)).natDegree := by
  apply le_natDegree_of_ne_zero
  rw [coeff_even_odd_pair]
  have hm : (2 * A.natDegree) % 2 = 0 := by omega
  have hd : (2 * A.natDegree) / 2 = A.natDegree := by omega
  simp only [hm, hd, ↓reduceIte]
  exact leadingCoeff_ne_zero.mpr hA

lemma two_mul_natDegree_add_one_le_even_odd {R : Type*} [CommRing R] (A B : R[X]) (hB : B ≠ 0) :
    2 * B.natDegree + 1 ≤ (A.comp (X ^ 2) + X * B.comp (X ^ 2)).natDegree := by
  apply le_natDegree_of_ne_zero
  rw [coeff_even_odd_pair]
  have hm : ¬ (2 * B.natDegree + 1) % 2 = 0 := by omega
  have hd : (2 * B.natDegree + 1) / 2 = B.natDegree := by omega
  simp only [hm, hd, ↓reduceIte]
  exact leadingCoeff_ne_zero.mpr hB

open Classical in
lemma natDegree_even_odd_le {R : Type*} [CommRing R] [IsDomain R] (A B : R[X]) :
    (A.comp (X ^ 2) + X * B.comp (X ^ 2)).natDegree ≤
      max (2 * A.natDegree) (if B = 0 then 0 else 2 * B.natDegree + 1) := by
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [natDegree_comp_X_sq]; exact le_max_left _ _
  · by_cases hB : B = 0
    · simp [hB]
    · simp only [hB, ↓reduceIte]
      have hne : B.comp (X ^ 2) ≠ 0 := mt (comp_X_sq_eq_zero_iff B).mp hB
      rw [natDegree_X_mul hne, natDegree_comp_X_sq]; exact le_max_right _ _

lemma derivative_comp_X_sq_char2 {R : Type*} [CommRing R] [CharP R 2] (p : R[X]) :
    (p.comp (X ^ 2)).derivative = 0 := by
  ext n
  rw [coeff_derivative, coeff_zero]
  by_cases h : (n + 1) % 2 = 0
  · have hcast : ((n : R) + 1) = 0 := by
      have hdiv : n + 1 = 2 * ((n + 1) / 2) := by omega
      have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
      calc (n : R) + 1 = ((n + 1 : ℕ) : R) := by push_cast; rfl
        _ = ((2 * ((n + 1) / 2) : ℕ) : R) := congrArg Nat.cast hdiv
        _ = (2 : R) * (((n + 1) / 2 : ℕ) : R) := by push_cast; rfl
        _ = 0 := by rw [h2, zero_mul]
    rw [hcast, mul_zero]
  · have hn : n + 1 = 2 * ((n + 1) / 2) + 1 := by omega
    rw [hn, comp_X_sq_coeff_odd, zero_mul]

lemma derivative_even_odd_char2 {R : Type*} [CommRing R] [CharP R 2] (A B : R[X]) :
    (A.comp (X ^ 2) + X * B.comp (X ^ 2)).derivative = B.comp (X ^ 2) := by
  rw [derivative_add, derivative_comp_X_sq_char2, zero_add, derivative_mul, derivative_X, one_mul,
    derivative_comp_X_sq_char2, mul_zero, add_zero]

/-- Even-degree half of `p : F[X]`. -/
noncomputable def evenPart {F : Type*} [Semiring F] (p : F[X]) : F[X] :=
  ∑ k ∈ Finset.range (p.natDegree / 2 + 1), monomial k (p.coeff (2 * k))

/-- Odd-degree half of `p : F[X]`. -/
noncomputable def oddPart {F : Type*} [Semiring F] (p : F[X]) : F[X] :=
  ∑ k ∈ Finset.range (p.natDegree / 2 + 1), monomial k (p.coeff (2 * k + 1))

lemma coeff_evenPart {F : Type*} [Semiring F] (p : F[X]) (k : ℕ) :
    (evenPart p).coeff k = p.coeff (2 * k) := by
  unfold evenPart; rw [finset_sum_coeff]
  by_cases hk : k < p.natDegree / 2 + 1
  · rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hne; simp [coeff_monomial, hne]
    · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    apply Finset.sum_eq_zero; intro m hm
    have := Finset.mem_range.mp hm
    simp [coeff_monomial, show m ≠ k by omega]

lemma coeff_oddPart {F : Type*} [Semiring F] (p : F[X]) (k : ℕ) :
    (oddPart p).coeff k = p.coeff (2 * k + 1) := by
  unfold oddPart; rw [finset_sum_coeff]
  by_cases hk : k < p.natDegree / 2 + 1
  · rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hne; simp [coeff_monomial, hne]
    · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    apply Finset.sum_eq_zero; intro m hm
    have := Finset.mem_range.mp hm
    simp [coeff_monomial, show m ≠ k by omega]

lemma evenPart_add_X_oddPart {R : Type*} [CommRing R] (p : R[X]) :
    (evenPart p).comp (X ^ 2) + X * (oddPart p).comp (X ^ 2) = p := by
  ext n
  rw [coeff_even_odd_pair, coeff_evenPart, coeff_oddPart]
  split_ifs with h
  · rw [show 2 * (n / 2) = n by omega]
  · rw [show 2 * (n / 2) + 1 = n by omega]

lemma derivative_eq_zero_iff_sq (p : Fld[X]) : p.derivative = 0 ↔ ∃ q : Fld[X], p = q ^ 2 := by
  constructor
  · intro hd
    have hodd : oddPart p = 0 := by
      have h1 := congrArg Polynomial.derivative (evenPart_add_X_oddPart p)
      rw [derivative_even_odd_char2, hd] at h1
      exact (comp_X_sq_eq_zero_iff (oddPart p)).mp h1
    refine ⟨sqrtPoly (evenPart p), ?_⟩
    rw [sqrtPoly_sq]
    have h2 := evenPart_add_X_oddPart p
    rw [hodd, zero_comp, mul_zero, add_zero] at h2
    exact h2.symm
  · rintro ⟨q, rfl⟩
    rw [sq, derivative_mul, show q.derivative * q + q * q.derivative = q.derivative * q + q.derivative * q by ring]
    exact CharTwo.add_self_eq_zero _

end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
