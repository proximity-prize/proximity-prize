import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import ProximityPrize.SubmissionBinaryLower.B6401IntFarkas
import ProximityPrize.SubmissionBinaryLower.B6401T4Rows
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
1. `SparseRow` / `baseT4Rows` satisfaction bridge matching `B6401IntFarkas.checkT4Bucket_sound`
   and `B6401T4Rows.buildT4ARows` / `buildT4BRows` definitionally.
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
namespace B6401Table4Common

open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401Params hiding D
open B6401KerDOrders B6401IntFarkas B6401T4Rows
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
`B6401IntFarkas.checkT4Bucket_sound`. -/
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

private theorem baseT4Rows_sat_aux {nv ic : ℕ} (hic : 9 ≤ ic) (hic_lt : ic < nv)
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

/-- Universal divisibility-sum bound: if `(X - C (f i))^(m i) ∣ p` for an injective `f` on `S`
and `p ≠ 0`, then `∑ i ∈ S, m i ≤ p.natDegree`. -/
theorem sum_ord_le_natDegree_of_dvd {ι : Type*} {F : Type*} [Field F]
    (S : Finset ι) (f : ι → F) (hf : Function.Injective f)
    (p : F[X]) (hp : p ≠ 0) (m : ι → ℕ)
    (hdvd : ∀ i ∈ S, (X - C (f i)) ^ m i ∣ p) :
    ∑ i ∈ S, m i ≤ p.natDegree := by
  have hprod : (∏ i ∈ S, (X - C (f i)) ^ m i) ∣ p := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      apply IsCoprime.pow
      have hne : f j - f i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hf h.symm))
      refine ⟨C (f j - f i)⁻¹, -C (f j - f i)⁻¹, ?_⟩
      calc C (f j - f i)⁻¹ * (X - C (f i)) + -C (f j - f i)⁻¹ * (X - C (f j))
          = C (f j - f i)⁻¹ * C (f j - f i) := by rw [map_sub]; ring
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hne, map_one]
    · exact hdvd
  have hdeg : (∏ i ∈ S, (X - C (f i)) ^ m i).natDegree = ∑ i ∈ S, m i := by
    rw [natDegree_prod _ _ (fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _))]
    apply Finset.sum_congr rfl; intro i _
    rw [natDegree_pow (X - C (f i)) (m i), natDegree_X_sub_C, mul_one]
  rw [← hdeg]
  exact natDegree_le_of_dvd hprod hp

/-- Specialization to `rootMultiplicity` along any injective `f : ι → F`. -/
theorem sum_rootMultiplicity_le_natDegree {ι : Type*} {F : Type*} [Field F]
    (S : Finset ι) (f : ι → F) (hf : Function.Injective f) (p : F[X]) (hp : p ≠ 0) :
    ∑ i ∈ S, p.rootMultiplicity (f i) ≤ p.natDegree :=
  sum_ord_le_natDegree_of_dvd S f hf p hp _ fun i _ => pow_rootMultiplicity_dvd p (f i)

lemma domain_sq_injective : Function.Injective (fun i : Idx => BinaryIRSProfile.domain i ^ 2) := by
  intro i j h
  have hfrob : frobenius Fld 2 (BinaryIRSProfile.domain i) = frobenius Fld 2 (BinaryIRSProfile.domain j) := by
    simpa [frobenius_def] using h
  exact BinaryIRSProfile.domain.injective (frobenius_inj Fld 2 hfrob)

lemma pow_dvd_comp_X_sq_iff (p : Fld[X]) (x : Fld) (m : ℕ) :
    (X - C x) ^ (2 * m) ∣ p.comp (X ^ 2) ↔ (X - C (x ^ 2)) ^ m ∣ p := by
  have hsq : (X - C x : Fld[X]) ^ 2 = X ^ 2 - C (x ^ 2) := by
    have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
    calc (X - C x : Fld[X]) ^ 2 = X ^ 2 - 2 * X * C x + C x ^ 2 := by ring
      _ = X ^ 2 + C (x ^ 2) := by rw [h2, map_pow]; ring
      _ = X ^ 2 - C (x ^ 2) := by rw [sub_eq_add_neg, CharTwo.neg_eq]
  constructor
  · rintro ⟨q, hq⟩
    have hsqrt : (X - C x) ^ m ∣ sqrtPoly p := by
      by_cases hp : p = 0
      · simp [hp, sqrtPoly]
      · have hsne : sqrtPoly p ≠ 0 := mt (sqrtPoly_eq_zero_iff p).mp hp
        rw [← le_rootMultiplicity_iff hsne]
        have hrm := (le_rootMultiplicity_iff (pow_ne_zero 2 hsne)).mpr
          (by rw [sqrtPoly_sq]; exact ⟨q, hq⟩)
        rw [sq, rootMultiplicity_mul (mul_ne_zero hsne hsne)] at hrm
        omega
    rcases hsqrt with ⟨r, hr⟩
    have hsq_eq := congrArg (· ^ 2) hr
    rw [sqrtPoly_sq, mul_pow, ← pow_mul, mul_comm m 2, pow_mul, hsq] at hsq_eq
    have h2r : ∀ r0 : Fld[X], r0 ^ 2 = (r0.map (frobenius Fld 2)).comp (X ^ 2) := fun r0 => by
      induction r0 using Polynomial.induction_on' with
      | add a b ha hb =>
          have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
          rw [Polynomial.map_add, add_comp, ← ha, ← hb]
          calc (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
            _ = a ^ 2 + b ^ 2 := by rw [h2]; ring
      | monomial k c =>
          rw [map_monomial, monomial_comp, monomial_pow, ← pow_mul, mul_comm 2 k,
            C_mul_X_pow_eq_monomial, frobenius_def]
    rw [h2r r] at hsq_eq
    refine ⟨r.map (frobenius Fld 2), ?_⟩
    have hcomp : p.comp (X ^ 2) = ((X - C (x ^ 2)) ^ m * r.map (frobenius Fld 2)).comp (X ^ 2) := by
      rw [mul_comp, pow_comp, sub_comp, X_comp, C_comp]; exact hsq_eq
    exact sub_eq_zero.mp ((comp_X_sq_eq_zero_iff _).mp (by rw [sub_comp, hcomp, sub_self]))
  · rintro ⟨q, rfl⟩
    refine ⟨q.comp (X ^ 2), ?_⟩
    rw [mul_comp, pow_comp, sub_comp, X_comp, C_comp, ← hsq, ← pow_mul]

lemma rootMultiplicity_comp_X_sq (p : Fld[X]) (hp : p ≠ 0) (x : Fld) :
    (p.comp (X ^ 2)).rootMultiplicity x = 2 * p.rootMultiplicity (x ^ 2) := by
  have hne : p.comp (X ^ 2) ≠ 0 := mt (comp_X_sq_eq_zero_iff p).mp hp
  have hsne : sqrtPoly p ≠ 0 := mt (sqrtPoly_eq_zero_iff p).mp hp
  have hrm_sq : (p.comp (X ^ 2)).rootMultiplicity x = 2 * (sqrtPoly p).rootMultiplicity x := by
    rw [← sqrtPoly_sq, sq, rootMultiplicity_mul (mul_ne_zero hsne hsne)]; omega
  rw [hrm_sq]
  apply congrArg (2 * ·)
  apply le_antisymm
  · rw [le_rootMultiplicity_iff hp, ← pow_dvd_comp_X_sq_iff]
    rw [← sqrtPoly_sq, mul_comm, pow_mul]
    exact pow_dvd_pow_of_dvd (pow_rootMultiplicity_dvd (sqrtPoly p) x) 2
  · rw [le_rootMultiplicity_iff hsne]
    have h := (pow_dvd_comp_X_sq_iff p x (p.rootMultiplicity (x ^ 2))).mpr (pow_rootMultiplicity_dvd p (x ^ 2))
    rw [← le_rootMultiplicity_iff hne, hrm_sq] at h
    exact (le_rootMultiplicity_iff hsne).mp (by omega)

lemma rootMultiplicity_sqrtPoly (p : Fld[X]) (hp : p ≠ 0) (x : Fld) :
    (sqrtPoly p).rootMultiplicity x = p.rootMultiplicity (x ^ 2) := by
  have hsne : sqrtPoly p ≠ 0 := mt (sqrtPoly_eq_zero_iff p).mp hp
  have h1 := rootMultiplicity_comp_X_sq p hp x
  rw [← sqrtPoly_sq, sq, rootMultiplicity_mul (mul_ne_zero hsne hsne)] at h1
  omega

lemma pow_dvd_of_shift_coeff_zero {F : Type*} [Field F] (p : F[X]) (a : F) (m : ℕ)
    (h : ∀ i < m, (p.comp (C a + X)).coeff i = 0) :
    (X - C a) ^ m ∣ p := by
  have hx : X ^ m ∣ p.comp (C a + X) := X_pow_dvd_iff.mpr h
  rcases hx with ⟨q, hq⟩
  refine ⟨q.comp (X - C a), ?_⟩
  have hb := congrArg (fun f : F[X] => f.comp (X - C a)) hq
  simp only [comp_assoc, add_comp, mul_comp, pow_comp, X_comp, C_comp, add_sub_cancel, comp_X] at hb
  exact hb

lemma shift_coeff_zero_of_pow_dvd {F : Type*} [Field F] (p : F[X]) (a : F) (m : ℕ)
    (h : (X - C a) ^ m ∣ p) :
    ∀ i < m, (p.comp (C a + X)).coeff i = 0 := by
  rcases h with ⟨q, rfl⟩
  rw [mul_comp, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_left]
  exact X_pow_dvd_iff.mp (dvd_mul_right _ _)

/-! ### Part 3: Quadratic Char-2 Resultant Identities via `AlgebraicClosure` -/

section QuadResultant

variable {K : Type*} [Field K] [CharP K 2]

private lemma quad_splits_algClosed (g0 g1 g2 : K) (hg2 : g2 ≠ 0) :
    let L := AlgebraicClosure K
    let ι : K →+* L := algebraMap K L
    ∃ (r1 r2 α β : L),
      α ^ 2 = r1 ∧ β ^ 2 = r2 ∧
      r1 + r2 = ι g1 / ι g2 ∧ r1 * r2 = ι g0 / ι g2 ∧
      (C g0 + C g1 * X + C g2 * X ^ 2).map ι = C (ι g2) * (X - C r1) * (X - C r2) ∧
      ((C g0 + C g1 * X + C g2 * X ^ 2).comp (X ^ 2)).map ι =
        C (ι g2) * ((X - C α) ^ 2 * (X - C β) ^ 2) := by
  intro L ι
  haveI : CharP L 2 := charP_of_injective_algebraMap ι.injective 2
  have h2L : (2 : L) = 0 := CharTwo.two_eq_zero
  have hnegL : ∀ u : L, -u = u := CharTwo.neg_eq
  have hg2L : ι g2 ≠ 0 := (map_ne_zero ι).mpr hg2
  set G : L[X] := (C g0 + C g1 * X + C g2 * X ^ 2).map ι
  have hGeq : G = C (ι g0) + C (ι g1) * X + C (ι g2) * X ^ 2 := by
    simp [G, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
  have hGdeg : G.degree ≠ 0 := by
    have hnd : G.natDegree = 2 := by
      apply le_antisymm
      · rw [hGeq]
        refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le (by simp)
          (natDegree_C_mul_le _ _ |>.trans (by simp)))) (natDegree_C_mul_le _ _ |>.trans (by simp)))
      · apply le_natDegree_of_ne_zero
        rw [hGeq]; simp [coeff_C, coeff_X, coeff_X_pow, hg2L]
    rw [degree_eq_natDegree (by intro h0; rw [h0, natDegree_zero] at hnd; omega), hnd]
    norm_num
  obtain ⟨r1, hr1⟩ := IsAlgClosed.exists_root G hGdeg
  have hr1_eq : ι g0 + ι g1 * r1 + ι g2 * r1 ^ 2 = 0 := by
    have h := hr1; rw [IsRoot.def, hGeq] at h; simpa using h
  set r2 : L := ι g1 / ι g2 + r1
  have hr_sum : r1 + r2 = ι g1 / ι g2 := by
    dsimp [r2]
    calc r1 + (ι g1 / ι g2 + r1) = ι g1 / ι g2 + (r1 + r1) := by ring
      _ = ι g1 / ι g2 := by rw [CharTwo.add_self_eq_zero, add_zero]
  have hr_prod : r1 * r2 = ι g0 / ι g2 := by
    have h1 : ι g2 * (r1 * r2) = ι g1 * r1 + ι g2 * r1 ^ 2 := by
      dsimp [r2]; field_simp [hg2L]
    have h2 : ι g1 * r1 + ι g2 * r1 ^ 2 = ι g0 := by
      have := congrArg (· + ι g0) hr1_eq
      calc ι g1 * r1 + ι g2 * r1 ^ 2
          = (ι g0 + ι g1 * r1 + ι g2 * r1 ^ 2) + ι g0 := by
            rw [show (ι g0 + ι g1 * r1 + ι g2 * r1 ^ 2) + ι g0 = (ι g0 + ι g0) + (ι g1 * r1 + ι g2 * r1 ^ 2) by ring,
              CharTwo.add_self_eq_zero, zero_add]
        _ = 0 + ι g0 := by rw [hr1_eq]
        _ = ι g0 := zero_add _
    rw [eq_div_iff hg2L, mul_comm, h1, h2]
  have hα_deg : (X ^ 2 - C r1 : L[X]).degree ≠ 0 := by
    have hnd : (X ^ 2 - C r1 : L[X]).natDegree = 2 := by
      rw [natDegree_sub_C, natDegree_X_pow]
    rw [degree_eq_natDegree (by intro h0; rw [h0, natDegree_zero] at hnd; omega), hnd]; norm_num
  have hβ_deg : (X ^ 2 - C r2 : L[X]).degree ≠ 0 := by
    have hnd : (X ^ 2 - C r2 : L[X]).natDegree = 2 := by
      rw [natDegree_sub_C, natDegree_X_pow]
    rw [degree_eq_natDegree (by intro h0; rw [h0, natDegree_zero] at hnd; omega), hnd]; norm_num
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (X ^ 2 - C r1 : L[X]) hα_deg
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (X ^ 2 - C r2 : L[X]) hβ_deg
  have hα2 : α ^ 2 = r1 := sub_eq_zero.mp (by simpa [IsRoot.def] using hα)
  have hβ2 : β ^ 2 = r2 := sub_eq_zero.mp (by simpa [IsRoot.def] using hβ)
  have hGfac : G = C (ι g2) * (X - C r1) * (X - C r2) := by
    rw [hGeq]
    have h1 : ι g2 * (r1 + r2) = ι g1 := by rw [hr_sum, mul_div_cancel₀ _ hg2L]
    have h2 : ι g2 * (r1 * r2) = ι g0 := by rw [hr_prod, mul_div_cancel₀ _ hg2L]
    calc C (ι g0) + C (ι g1) * X + C (ι g2) * X ^ 2
        = C (ι g2 * (r1 * r2)) + C (ι g2 * (r1 + r2)) * X + C (ι g2) * X ^ 2 := by rw [h1, h2]
      _ = C (ι g2) * (X ^ 2 + C (r1 + r2) * X + C (r1 * r2)) := by simp only [map_mul, map_add]; ring
      _ = C (ι g2) * (X - C r1) * (X - C r2) := by
          have hneg : ∀ p : L[X], -p = p := CharTwo.neg_eq
          simp only [sub_eq_add_neg, hneg, map_add, map_mul]; ring
  have hG2fac : ((C g0 + C g1 * X + C g2 * X ^ 2).comp (X ^ 2)).map ι =
      C (ι g2) * ((X - C α) ^ 2 * (X - C β) ^ 2) := by
    have hcomp : ((C g0 + C g1 * X + C g2 * X ^ 2).comp (X ^ 2)).map ι = G.comp (X ^ 2) := by
      simp [G, Polynomial.map_comp]
    rw [hcomp, hGfac]
    simp only [mul_comp, C_comp, sub_comp, X_comp]
    have hsq : ∀ u : L, (X - C u : L[X]) ^ 2 = X ^ 2 - C (u ^ 2) := fun u => by
      have h2p : (2 : L[X]) = 0 := CharTwo.two_eq_zero
      have hnegp : ∀ p : L[X], -p = p := CharTwo.neg_eq
      simp only [sub_eq_add_neg, hnegp]
      calc (X + C u : L[X]) ^ 2 = X ^ 2 + 2 * X * C u + C u ^ 2 := by ring
        _ = X ^ 2 + C (u ^ 2) := by rw [h2p, map_pow]; ring
    rw [← hα2, ← hβ2, ← hsq α, ← hsq β]; ring
  exact ⟨r1, r2, α, β, hα2, hβ2, hr_sum, hr_prod, hGfac, hG2fac⟩

/-- **Exact char-2 `(5, 4) ↔ (5, 2)` resultant reduction** (for weighted order bounds):
for `G = g0 + g1 V + g2 V^2` (`g2 ≠ 0`), `deg E, deg O ≤ 2`, and ANY `s : K`:
`s^4 * Res_Y^{(5, 4)}(E(Y^2) + Y O(Y^2), G(Y^2)) = Res_V^{(5, 2)}(s^2 E^2 + V (G + s O)^2, G)`. -/
theorem char2_resultant_5_4_eq_5_2 (E O : K[X]) (g0 g1 g2 s : K) (hg2 : g2 ≠ 0)
    (hE : E.natDegree ≤ 2) (hO : O.natDegree ≤ 2) :
    let G : K[X] := C g0 + C g1 * X + C g2 * X ^ 2
    s ^ 4 * Polynomial.resultant (E.comp (X ^ 2) + X * O.comp (X ^ 2)) (G.comp (X ^ 2)) 5 4 =
      Polynomial.resultant (C (s ^ 2) * E ^ 2 + X * (G + C s * O) ^ 2) G 5 2 := by
  intro G
  let L := AlgebraicClosure K
  let ι : K →+* L := algebraMap K L
  haveI : CharP L 2 := charP_of_injective_algebraMap ι.injective 2
  have hneg1 : (-1 : L) = 1 := by rw [CharTwo.neg_eq]
  obtain ⟨r1, r2, α, β, hα2, hβ2, _, _, hGfac, hG2fac⟩ := quad_splits_algClosed g0 g1 g2 hg2
  apply ι.injective
  rw [map_mul, map_pow, ← Polynomial.resultant_map_map, ← Polynomial.resultant_map_map]
  set f0L : L[X] := (E.comp (X ^ 2) + X * O.comp (X ^ 2)).map ι
  set ΨL : L[X] := (C (s ^ 2) * E ^ 2 + X * (G + C s * O) ^ 2).map ι
  have hf0deg : f0L.natDegree ≤ 5 := by
    refine natDegree_map_le.trans ((natDegree_add_le _ _).trans (max_le ?_ ?_))
    · rw [natDegree_comp_X_sq]; omega
    · refine natDegree_mul_le.trans ?_; rw [natDegree_X, natDegree_comp_X_sq]; omega
  have hΨdeg : ΨL.natDegree ≤ 5 := by
    have hGdeg : G.natDegree ≤ 2 :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans
        (max_le (by simp) (natDegree_C_mul_le _ _ |>.trans (by simp))))
        (natDegree_C_mul_le _ _ |>.trans (by simp)))
    have hGO : (G + C s * O).natDegree ≤ 2 :=
      (natDegree_add_le _ _).trans (max_le hGdeg ((natDegree_C_mul_le _ _).trans hO))
    refine natDegree_map_le.trans ((natDegree_add_le _ _).trans (max_le ?_ ?_))
    · exact (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by omega))
    · have hx1 : (X : K[X]).natDegree ≤ 1 := natDegree_X_le
      have hsq4 : ((G + C s * O) ^ 2).natDegree ≤ 4 := natDegree_pow_le.trans (by omega)
      exact natDegree_mul_le.trans (by omega)
  rw [show (G.comp (X ^ 2)).map ι = C (ι g2) * ((X - C α) ^ 2 * (X - C β) ^ 2) from hG2fac]
  rw [show G.map ι = C (ι g2) * ((X - C r1) * (X - C r2)) by rw [hGfac]; ring]
  have hdegα : ((X - C α : L[X]) ^ 2).natDegree = 2 := by rw [natDegree_pow, natDegree_X_sub_C]
  have hdegβ : ((X - C β : L[X]) ^ 2).natDegree = 2 := by rw [natDegree_pow, natDegree_X_sub_C]
  have hdegr1 : (X - C r1 : L[X]).natDegree = 1 := natDegree_X_sub_C r1
  have hdegr2 : (X - C r2 : L[X]).natDegree = 1 := natDegree_X_sub_C r2
  rw [Polynomial.resultant_C_mul_right, Polynomial.resultant_C_mul_right]
  conv_lhs =>
    rw [show (4 : ℕ) = ((X - C α : L[X]) ^ 2).natDegree + ((X - C β : L[X]) ^ 2).natDegree by omega,
      Polynomial.resultant_mul_right _ _ _ 5 hf0deg]
  conv_rhs =>
    rw [show (2 : ℕ) = (X - C r1 : L[X]).natDegree + (X - C r2 : L[X]).natDegree by omega,
      Polynomial.resultant_mul_right _ _ _ 5 hΨdeg]
  rw [hdegα, hdegβ, hdegr1, hdegr2,
    Polynomial.resultant_X_sub_C_pow_right f0L α 5 2 hf0deg,
    Polynomial.resultant_X_sub_C_pow_right f0L β 5 2 hf0deg,
    Polynomial.resultant_X_sub_C_right ΨL 5 r1 hΨdeg,
    Polynomial.resultant_X_sub_C_right ΨL 5 r2 hΨdeg, hneg1]
  simp only [one_pow, one_mul]
  have heval_pt : ∀ (u r : L), u ^ 2 = r → (G.map ι).eval r = 0 →
      (ι s) ^ 2 * (f0L.eval u) ^ 2 = ΨL.eval r := by
    intro u r hu hr
    have hf0u : f0L.eval u = (E.map ι).eval r + u * (O.map ι).eval r := by
      simp only [f0L, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_comp,
        Polynomial.map_pow, eval_add, eval_mul, eval_X, eval_comp, eval_pow, hu]
    have hΨr : ΨL.eval r = (ι s) ^ 2 * ((E.map ι).eval r) ^ 2 + r * ((G.map ι).eval r + ι s * (O.map ι).eval r) ^ 2 := by
      simp only [ΨL, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
        Polynomial.map_X, eval_add, eval_mul, eval_pow, eval_C, eval_X, map_pow]
    rw [hf0u, hΨr, hr, zero_add]
    have h2L : (2 : L) = 0 := CharTwo.two_eq_zero
    calc (ι s) ^ 2 * ((E.map ι).eval r + u * (O.map ι).eval r) ^ 2
        = (ι s) ^ 2 * (((E.map ι).eval r) ^ 2 + 2 * (E.map ι).eval r * (u * (O.map ι).eval r) +
            u ^ 2 * ((O.map ι).eval r) ^ 2) := by ring
      _ = (ι s) ^ 2 * ((E.map ι).eval r) ^ 2 + r * (ι s * (O.map ι).eval r) ^ 2 := by
          rw [h2L, hu]; ring
  have hr1_0 : (G.map ι).eval r1 = 0 := by rw [hGfac]; simp
  have hr2_0 : (G.map ι).eval r2 = 0 := by rw [hGfac]; simp
  have h1 := heval_pt α r1 hα2 hr1_0
  have h2 := heval_pt β r2 hβ2 hr2_0
  calc ι s ^ 4 * (ι g2 ^ 5 * (f0L.eval α ^ 2 * f0L.eval β ^ 2))
      = ι g2 ^ 5 * ((ι s ^ 2 * f0L.eval α ^ 2) * (ι s ^ 2 * f0L.eval β ^ 2)) := by ring
    _ = ι g2 ^ 5 * (ΨL.eval r1 * ΨL.eval r2) := by rw [h1, h2]

/-- **Exact char-2 `det M = 0, p ≠ 0` resultant factorization** over any char-2 field `K`:
`Res_Y^{(5, 4)}(f_0, f_1) = (p^4 g_0 + p^2 r_val^2 g_1 + r_val^4 g_2) * (M20^2 + M21 M10)^2`! -/
theorem char2_resultant_5_4_syzygy_factor
    (P0 P1 P2 C0 C1 C2 B0 B1 B2 p c b xVar M21 M20 M10 : K)
    (hp : p ≠ 0) (hg2 : C2 + xVar * B2 ≠ 0)
    (hsyz0 : p * P0 + c * C0 + b * B0 = 0)
    (hsyz1 : p * P1 + c * C1 + b * B1 = 0)
    (hsyz2 : p * P2 + c * C2 + b * B2 = 0)
    (hM21 : p * M21 = C2 * B1 + C1 * B2)
    (hM20 : p * M20 = C2 * B0 + C0 * B2)
    (hM10 : p * M10 = C1 * B0 + C0 * B1) :
    let g0 := C0 + xVar * B0
    let g1 := C1 + xVar * B1
    let g2 := C2 + xVar * B2
    let rVal := b + xVar * c
    let E : K[X] := C P0 + C P1 * X + C P2 * X ^ 2
    let O : K[X] := C B0 + C B1 * X + C B2 * X ^ 2
    let G : K[X] := C g0 + C g1 * X + C g2 * X ^ 2
    Polynomial.resultant (E.comp (X ^ 2) + X * O.comp (X ^ 2)) (G.comp (X ^ 2)) 5 4 =
      (p ^ 4 * g0 + p ^ 2 * rVal ^ 2 * g1 + rVal ^ 4 * g2) * (M20 ^ 2 + M21 * M10) ^ 2 := by
  intro g0 g1 g2 rVal E O G
  let L := AlgebraicClosure K
  let ι : K →+* L := algebraMap K L
  haveI : CharP L 2 := charP_of_injective_algebraMap ι.injective 2
  have h2L : (2 : L) = 0 := CharTwo.two_eq_zero
  have hneg1 : (-1 : L) = 1 := by rw [CharTwo.neg_eq]
  have hpL : ι p ≠ 0 := by simp [hp]
  have hg2L : ι g2 ≠ 0 := (map_ne_zero ι).mpr hg2
  obtain ⟨r1, r2, α, β, hα2, hβ2, hr_sum, hr_prod, hGfac, hG2fac⟩ := quad_splits_algClosed g0 g1 g2 hg2
  apply ι.injective
  rw [← Polynomial.resultant_map_map]
  set f0L : L[X] := (E.comp (X ^ 2) + X * O.comp (X ^ 2)).map ι
  have hf0deg : f0L.natDegree ≤ 5 := by
    have hE : E.natDegree ≤ 2 :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans
        (max_le (by simp) (natDegree_C_mul_le _ _ |>.trans (by simp))))
        (natDegree_C_mul_le _ _ |>.trans (by simp)))
    have hO : O.natDegree ≤ 2 :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans
        (max_le (by simp) (natDegree_C_mul_le _ _ |>.trans (by simp))))
        (natDegree_C_mul_le _ _ |>.trans (by simp)))
    refine natDegree_map_le.trans ((natDegree_add_le _ _).trans (max_le ?_ ?_))
    · rw [natDegree_comp_X_sq]; omega
    · refine natDegree_mul_le.trans ?_; rw [natDegree_X, natDegree_comp_X_sq]; omega
  rw [show (G.comp (X ^ 2)).map ι = C (ι g2) * ((X - C α) ^ 2 * (X - C β) ^ 2) from hG2fac]
  have hdegα : ((X - C α : L[X]) ^ 2).natDegree = 2 := by rw [natDegree_pow, natDegree_X_sub_C]
  have hdegβ : ((X - C β : L[X]) ^ 2).natDegree = 2 := by rw [natDegree_pow, natDegree_X_sub_C]
  rw [Polynomial.resultant_C_mul_right,
    show (4 : ℕ) = ((X - C α : L[X]) ^ 2).natDegree + ((X - C β : L[X]) ^ 2).natDegree by omega,
    Polynomial.resultant_mul_right _ _ _ 5 hf0deg, hdegα, hdegβ,
    Polynomial.resultant_X_sub_C_pow_right f0L α 5 2 hf0deg,
    Polynomial.resultant_X_sub_C_pow_right f0L β 5 2 hf0deg, hneg1]
  simp only [one_pow, one_mul]
  -- At any root u (u^2 = r) of G, p^2 * f0(u)^2 = (p^2 * r + rVal^2) * O(r)^2!
  have hroot_sq : ∀ (u r : L), u ^ 2 = r → (G.map ι).eval r = 0 →
      (ι p) ^ 2 * (f0L.eval u) ^ 2 = ((ι p) ^ 2 * r + (ι rVal) ^ 2) * ((O.map ι).eval r) ^ 2 := by
    intro u r hu hr
    have hGr : ι g0 + ι g1 * r + ι g2 * r ^ 2 = 0 := by
      simpa [G, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow] using hr
    have hE_eq : ι p * (E.map ι).eval r = ι c * (ι g0 + ι g1 * r + ι g2 * r ^ 2) + ι rVal * (O.map ι).eval r := by
      have hs0 : ι p * ι P0 = ι c * ι C0 + ι b * ι B0 := by
        have := congrArg ι hsyz0; simp only [map_add, map_mul, map_zero] at this
        have hadd := congrArg (· + (ι c * ι C0 + ι b * ι B0)) this
        have hca : (ι c * ι C0 + ι b * ι B0) + (ι c * ι C0 + ι b * ι B0) = 0 := CharTwo.add_self_eq_zero _
        linear_combination hadd - hca
      have hs1 : ι p * ι P1 = ι c * ι C1 + ι b * ι B1 := by
        have := congrArg ι hsyz1; simp only [map_add, map_mul, map_zero] at this
        have hadd := congrArg (· + (ι c * ι C1 + ι b * ι B1)) this
        have hca : (ι c * ι C1 + ι b * ι B1) + (ι c * ι C1 + ι b * ι B1) = 0 := CharTwo.add_self_eq_zero _
        linear_combination hadd - hca
      have hs2 : ι p * ι P2 = ι c * ι C2 + ι b * ι B2 := by
        have := congrArg ι hsyz2; simp only [map_add, map_mul, map_zero] at this
        have hadd := congrArg (· + (ι c * ι C2 + ι b * ι B2)) this
        have hca : (ι c * ι C2 + ι b * ι B2) + (ι c * ι C2 + ι b * ι B2) = 0 := CharTwo.add_self_eq_zero _
        linear_combination hadd - hca
      simp only [E, O, g0, g1, g2, rVal, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_C, Polynomial.map_X, eval_add, eval_mul, eval_pow, eval_C, eval_X, map_add, map_mul]
      have h2x : ∀ t : L, t + t = 0 := CharTwo.add_self_eq_zero
      have hz0 : ι c * ι xVar * ι B0 + ι c * ι xVar * ι B0 = 0 := h2x _
      have hz1 : ι c * ι xVar * ι B1 * r + ι c * ι xVar * ι B1 * r = 0 := h2x _
      have hz2 : ι c * ι xVar * ι B2 * r ^ 2 + ι c * ι xVar * ι B2 * r ^ 2 = 0 := h2x _
      linear_combination hs0 + r * hs1 + r ^ 2 * hs2 - hz0 - hz1 - hz2
    have hpf0 : ι p * f0L.eval u = (ι p * u + ι rVal) * (O.map ι).eval r := by
      have hf0u : f0L.eval u = (E.map ι).eval r + u * (O.map ι).eval r := by
        simp only [f0L, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_comp,
          Polynomial.map_pow, eval_add, eval_mul, eval_X, eval_comp, eval_pow, hu]
      rw [hf0u, mul_add, hE_eq, hGr, mul_zero, zero_add]; ring
    have hsq : (ι p * u + ι rVal) ^ 2 = (ι p) ^ 2 * r + (ι rVal) ^ 2 := by
      calc (ι p * u + ι rVal) ^ 2 = (ι p) ^ 2 * u ^ 2 + 2 * (ι p * u) * ι rVal + (ι rVal) ^ 2 := by ring
        _ = (ι p) ^ 2 * r + (ι rVal) ^ 2 := by rw [h2L, hu]; ring
    calc (ι p) ^ 2 * (f0L.eval u) ^ 2 = (ι p * f0L.eval u) ^ 2 := by ring
      _ = ((ι p * u + ι rVal) * (O.map ι).eval r) ^ 2 := by rw [hpf0]
      _ = ((ι p) ^ 2 * r + (ι rVal) ^ 2) * ((O.map ι).eval r) ^ 2 := by rw [mul_pow, hsq]
  have hr1_0 : (G.map ι).eval r1 = 0 := by rw [hGfac]; simp
  have hr2_0 : (G.map ι).eval r2 = 0 := by rw [hGfac]; simp
  have hsq1 := hroot_sq α r1 hα2 hr1_0
  have hsq2 := hroot_sq β r2 hβ2 hr2_0
  -- Vieta part 1: g2 * (p^2 r1 + rVal^2) * (p^2 r2 + rVal^2) = p^4 g0 + p^2 rVal^2 g1 + rVal^4 g2
  have hV1 : ι g2 * ((ι p) ^ 2 * r1 + (ι rVal) ^ 2) * ((ι p) ^ 2 * r2 + (ι rVal) ^ 2) =
      (ι p) ^ 4 * ι g0 + (ι p) ^ 2 * (ι rVal) ^ 2 * ι g1 + (ι rVal) ^ 4 * ι g2 := by
    have h1 : ι g2 * (r1 + r2) = ι g1 := by rw [hr_sum, mul_div_cancel₀ _ hg2L]
    have h2 : ι g2 * (r1 * r2) = ι g0 := by rw [hr_prod, mul_div_cancel₀ _ hg2L]
    linear_combination (ι p) ^ 4 * h2 + (ι p) ^ 2 * (ι rVal) ^ 2 * h1
  -- Vieta part 2: g2^2 * O(r1) * O(r2) = p^2 * (M20^2 + M21 * M10)
  have hV2 : (ι g2) ^ 2 * (O.map ι).eval r1 * (O.map ι).eval r2 =
      (ι p) ^ 2 * ((ι M20) ^ 2 + ι M21 * ι M10) := by
    have h1 : ι g2 * (r1 + r2) = ι g1 := by rw [hr_sum, mul_div_cancel₀ _ hg2L]
    have h2 : ι g2 * (r1 * r2) = ι g0 := by rw [hr_prod, mul_div_cancel₀ _ hg2L]
    have hsq_sum : (ι g2) ^ 2 * (r1 ^ 2 + r2 ^ 2) = (ι g1) ^ 2 := by
      have : (r1 + r2) ^ 2 = r1 ^ 2 + r2 ^ 2 := by
        calc (r1 + r2) ^ 2 = r1 ^ 2 + 2 * r1 * r2 + r2 ^ 2 := by ring
          _ = r1 ^ 2 + r2 ^ 2 := by rw [h2L]; ring
      calc (ι g2) ^ 2 * (r1 ^ 2 + r2 ^ 2) = (ι g2 * (r1 + r2)) ^ 2 := by rw [mul_pow, this]
        _ = (ι g1) ^ 2 := by rw [h1]
    have hO1 : (O.map ι).eval r1 = ι B0 + ι B1 * r1 + ι B2 * r1 ^ 2 := by
      simp [O, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
    have hO2 : (O.map ι).eval r2 = ι B0 + ι B1 * r2 + ι B2 * r2 ^ 2 := by
      simp [O, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
    have hM21L : ι g2 * ι B1 + ι g1 * ι B2 = ι p * ι M21 := by
      have := congrArg ι hM21; simp only [map_add, map_mul] at this
      simp only [g1, g2, map_add, map_mul]
      have hz := CharTwo.add_self_eq_zero (ι xVar * ι B2 * ι B1)
      linear_combination -this + hz
    have hM20L : ι g2 * ι B0 + ι g0 * ι B2 = ι p * ι M20 := by
      have := congrArg ι hM20; simp only [map_add, map_mul] at this
      simp only [g0, g2, map_add, map_mul]
      have hz := CharTwo.add_self_eq_zero (ι xVar * ι B2 * ι B0)
      linear_combination -this + hz
    have hM10L : ι g1 * ι B0 + ι g0 * ι B1 = ι p * ι M10 := by
      have := congrArg ι hM10; simp only [map_add, map_mul] at this
      simp only [g0, g1, map_add, map_mul]
      have hz := CharTwo.add_self_eq_zero (ι xVar * ι B1 * ι B0)
      linear_combination -this + hz
    rw [hO1, hO2]
    have hexp : (ι g2) ^ 2 * (ι B0 + ι B1 * r1 + ι B2 * r1 ^ 2) * (ι B0 + ι B1 * r2 + ι B2 * r2 ^ 2) =
        (ι g2 * ι B0 + ι g0 * ι B2) ^ 2 + (ι g2 * ι B1 + ι g1 * ι B2) * (ι g1 * ι B0 + ι g0 * ι B1) := by
      have h2m : ∀ t : L, 2 * t = 0 := fun t => by rw [h2L, zero_mul]
      have hz1 := h2m (ι g2 * ι g0 * ι B0 * ι B2)
      have hz2 := h2m (ι g2 * ι g1 * ι g0 * ι B1 * ι B2)
      -- Wait: simplify using (g2 * (r1 + r2) = g1, g2 * (r1 * r2) = g0, g2^2 * (r1^2 + r2^2) = g1^2)!
      have hr12_cube : (ι g2) ^ 2 * (r1 * r2 * (r1 + r2)) = ι g0 * ι g1 := by
        calc (ι g2) ^ 2 * (r1 * r2 * (r1 + r2)) = (ι g2 * (r1 * r2)) * (ι g2 * (r1 + r2)) := by ring
          _ = ι g0 * ι g1 := by rw [h2, h1]
      have hr12_sq : (ι g2) ^ 2 * (r1 * r2) ^ 2 = (ι g0) ^ 2 := by
        calc (ι g2) ^ 2 * (r1 * r2) ^ 2 = (ι g2 * (r1 * r2)) ^ 2 := by ring
          _ = (ι g0) ^ 2 := by rw [h2]
      have hmid : (ι g2) ^ 2 * (ι B0 + ι B1 * r1 + ι B2 * r1 ^ 2) * (ι B0 + ι B1 * r2 + ι B2 * r2 ^ 2) =
          (ι g2) ^ 2 * (ι B0) ^ 2 + ι g2 * ι B0 * ι B1 * (ι g2 * (r1 + r2)) +
          ι B0 * ι B2 * ((ι g2) ^ 2 * (r1 ^ 2 + r2 ^ 2)) + ι g2 * (ι B1) ^ 2 * (ι g2 * (r1 * r2)) +
          ι B1 * ι B2 * ((ι g2) ^ 2 * (r1 * r2 * (r1 + r2))) + (ι B2) ^ 2 * ((ι g2) ^ 2 * (r1 * r2) ^ 2) := by ring
      rw [hmid, h1, h2, hsq_sum, hr12_cube, hr12_sq]
      linear_combination -hz1
    rw [hexp, hM20L, hM21L, hM10L]; ring
  apply mul_left_cancel₀ (pow_ne_zero 4 hpL)
  simp only [map_mul, map_add, map_pow]
  calc ι p ^ 4 * (ι g2 ^ 5 * (f0L.eval α ^ 2 * f0L.eval β ^ 2))
      = ι g2 ^ 5 * ((ι p ^ 2 * f0L.eval α ^ 2) * (ι p ^ 2 * f0L.eval β ^ 2)) := by ring
    _ = ι g2 ^ 5 * ((((ι p) ^ 2 * r1 + (ι rVal) ^ 2) * ((O.map ι).eval r1) ^ 2) *
          (((ι p) ^ 2 * r2 + (ι rVal) ^ 2) * ((O.map ι).eval r2) ^ 2)) := by rw [hsq1, hsq2]
    _ = (ι g2 * ((ι p) ^ 2 * r1 + (ι rVal) ^ 2) * ((ι p) ^ 2 * r2 + (ι rVal) ^ 2)) *
          ((ι g2) ^ 2 * (O.map ι).eval r1 * (O.map ι).eval r2) ^ 2 := by ring
    _ = ((ι p) ^ 4 * ι g0 + (ι p) ^ 2 * (ι rVal) ^ 2 * ι g1 + (ι rVal) ^ 4 * ι g2) *
          ((ι p) ^ 2 * ((ι M20) ^ 2 + ι M21 * ι M10)) ^ 2 := by rw [hV1, hV2]
    _ = ι p ^ 4 * (((ι p) ^ 4 * ι g0 + (ι p) ^ 2 * (ι rVal) ^ 2 * ι g1 + (ι rVal) ^ 4 * ι g2) *
          ((ι M20) ^ 2 + ι M21 * ι M10) ^ 2) := by ring

end QuadResultant

private lemma res_5_4_eq_5_2_of_inj {K : Type*} [Field K] [CharP K 2]
    (ι : Fld[X] →+* K) (hι : Function.Injective ι)
    (Esh Osh A1s Gsh Ψ : BiPoly Fld)
    (hEdeg : Esh.natDegree ≤ 2) (hOdeg : Osh.natDegree ≤ 2) (hGdeg : Gsh.natDegree ≤ 2)
    (hg2_sh_ne : Gsh.coeff 2 ≠ 0)
    (hG_add : Gsh + C X * Osh = A1s)
    (hΨ_eq : Ψ = C (X ^ 2) * Esh ^ 2 + X * A1s ^ 2) :
    X ^ 4 * Polynomial.resultant (Esh.comp (X ^ 2) + X * Osh.comp (X ^ 2)) (Gsh.comp (X ^ 2)) 5 4 =
      Polynomial.resultant Ψ Gsh 5 2 := by
  apply hι
  rw [map_mul, map_pow, ← Polynomial.resultant_map_map, ← Polynomial.resultant_map_map]
  have hG_exp : Gsh = C (Gsh.coeff 0) + C (Gsh.coeff 1) * X + C (Gsh.coeff 2) * X ^ 2 := by
    ext m; cases m with
    | zero => simp [coeff_C, coeff_X, coeff_X_pow]
    | succ m' => cases m' with
      | zero => simp [coeff_C, coeff_X, coeff_X_pow]
      | succ m'' => cases m'' with
        | zero => simp [coeff_C, coeff_X, coeff_X_pow]
        | succ m''' =>
            rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hGdeg (by omega))]
            simp [coeff_C, coeff_X, coeff_X_pow]
  have hid := char2_resultant_5_4_eq_5_2 (Esh.map ι) (Osh.map ι)
    (ι (Gsh.coeff 0)) (ι (Gsh.coeff 1)) (ι (Gsh.coeff 2)) (ι X)
    (by intro h0; exact hg2_sh_ne (hι (by rw [map_zero]; exact h0)))
    (natDegree_map_le.trans hEdeg) (natDegree_map_le.trans hOdeg)
  have hGmap : Gsh.map ι = C (ι (Gsh.coeff 0)) + C (ι (Gsh.coeff 1)) * X + C (ι (Gsh.coeff 2)) * X ^ 2 := by
    conv_lhs => rw [hG_exp]
    simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
  have hf0map : (Esh.comp (X ^ 2) + X * Osh.comp (X ^ 2)).map ι =
      (Esh.map ι).comp (X ^ 2) + X * (Osh.map ι).comp (X ^ 2) := by
    simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_comp, Polynomial.map_pow]
  have hf1map : (Gsh.comp (X ^ 2)).map ι = (Gsh.map ι).comp (X ^ 2) := by
    simp [Polynomial.map_comp, Polynomial.map_pow]
  have hΨmap : Ψ.map ι = C ((ι X) ^ 2) * (Esh.map ι) ^ 2 + X * (Gsh.map ι + C (ι X) * Osh.map ι) ^ 2 := by
    have hA1map : A1s.map ι = Gsh.map ι + C (ι X) * Osh.map ι := by
      rw [← hG_add]; simp [Polynomial.map_add, Polynomial.map_mul]
    rw [hΨ_eq, ← hA1map]; simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
  rw [hf0map, hf1map, hΨmap, hGmap]
  exact hid

private lemma exists_poly_syzygy_of_det_zero {K : Type*} [Field K]
    (ι : Fld[X] →+* K) (hι : Function.Injective ι)
    (hsurj : ∀ x : K, ∃ n d : Fld[X], d ≠ 0 ∧ x * ι d = ι n)
    (M : Matrix (Fin 3) (Fin 3) Fld[X]) (hdet0 : M.det = 0) :
    ∃ p0 c0 b0 : Fld[X],
      (p0 ≠ 0 ∨ c0 ≠ 0 ∨ b0 ≠ 0) ∧
      ∀ j : Fin 3, p0 * M j 0 + c0 * M j 1 + b0 * M j 2 = 0 := by
  let MK : Matrix (Fin 3) (Fin 3) K := M.map ι
  have hdetK : MK.det = 0 := by
    change (ι.mapMatrix M).det = 0
    rw [← RingHom.map_det, hdet0, map_zero]
  obtain ⟨v, hv_ne, hv_mul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetK
  obtain ⟨n0, d0, hd0_ne, hd0⟩ := hsurj (v 0)
  obtain ⟨n1, d1, hd1_ne, hd1⟩ := hsurj (v 1)
  obtain ⟨n2, d2, hd2_ne, hd2⟩ := hsurj (v 2)
  set p0 : Fld[X] := n0 * d1 * d2
  set c0 : Fld[X] := d0 * n1 * d2
  set b0 : Fld[X] := d0 * d1 * n2
  refine ⟨p0, c0, b0, ?_, ?_⟩
  · by_contra hall; push Not at hall
    rcases hall with ⟨hp0, hc0, hb0⟩
    apply hv_ne; ext r; fin_cases r
    · have hn0 : n0 = 0 := by
        rcases mul_eq_zero.mp hp0 with h | h
        · exact (mul_eq_zero.mp h).resolve_right hd1_ne
        · exact absurd h hd2_ne
      rw [hn0, map_zero] at hd0
      exact (mul_eq_zero.mp hd0).resolve_right (fun h => hd0_ne (hι (by rw [map_zero]; exact h)))
    · have hn1 : n1 = 0 := by
        rcases mul_eq_zero.mp hc0 with h | h
        · exact (mul_eq_zero.mp h).resolve_left hd0_ne
        · exact absurd h hd2_ne
      rw [hn1, map_zero] at hd1
      exact (mul_eq_zero.mp hd1).resolve_right (fun h => hd1_ne (hι (by rw [map_zero]; exact h)))
    · have hn2 : n2 = 0 := by
        rcases mul_eq_zero.mp hb0 with h | h
        · exact absurd h (mul_ne_zero hd0_ne hd1_ne)
        · exact h
      rw [hn2, map_zero] at hd2
      exact (mul_eq_zero.mp hd2).resolve_right (fun h => hd2_ne (hι (by rw [map_zero]; exact h)))
  · intro j
    apply hι; rw [map_zero, map_add, map_add, map_mul ι p0, map_mul ι c0, map_mul ι b0]
    have hrow := congrFun hv_mul j
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, MK, Matrix.map_apply, Pi.zero_apply] at hrow
    have hm := congrArg (· * (ι d0 * ι d1 * ι d2)) hrow
    rw [zero_mul] at hm
    have h0' : ι p0 = v 0 * (ι d0 * ι d1 * ι d2) := by dsimp [p0]; simp only [map_mul]; rw [← hd0]; ring
    have h1' : ι c0 = v 1 * (ι d0 * ι d1 * ι d2) := by dsimp [c0]; simp only [map_mul]; rw [← hd1]; ring
    have h2' : ι b0 = v 2 * (ι d0 * ι d1 * ι d2) := by dsimp [b0]; simp only [map_mul]; rw [← hd2]; ring
    rw [h0', h1', h2']
    linear_combination hm

private lemma isCoprime_of_forall_dvd_isUnit_poly {K : Type*} [Field K] [DecidableEq K]
    {a b : K[X]} (h : ∀ d : K[X], d ∣ a → d ∣ b → IsUnit d) : IsCoprime a b := by
  have hu := h (EuclideanDomain.gcd a b) (EuclideanDomain.gcd_dvd_left a b) (EuclideanDomain.gcd_dvd_right a b)
  obtain ⟨u, hu'⟩ := hu
  have hbez := EuclideanDomain.gcd_eq_gcd_ab a b
  rw [← hu'] at hbez
  refine ⟨EuclideanDomain.gcdA a b * (u⁻¹ : K[X]ˣ), EuclideanDomain.gcdB a b * (u⁻¹ : K[X]ˣ), ?_⟩
  calc EuclideanDomain.gcdA a b * ↑u⁻¹ * a + EuclideanDomain.gcdB a b * ↑u⁻¹ * b
      = (a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b) * ↑u⁻¹ := by ring
    _ = ↑u * ↑u⁻¹ := by rw [← hbez]
    _ = 1 := Units.mul_inv u

private lemma coprime_triple_of_nonzero_poly {K : Type*} [Field K] [DecidableEq K]
    {p0 c0 b0 : K[X]} (hne0 : p0 ≠ 0 ∨ c0 ≠ 0 ∨ b0 ≠ 0) :
    ∃ g p c b : K[X],
      g ≠ 0 ∧ p0 = g * p ∧ c0 = g * c ∧ b0 = g * b ∧
      (p ≠ 0 ∨ c ≠ 0 ∨ b ≠ 0) ∧ (∀ d : K[X], d ∣ p → d ∣ c → d ∣ b → IsUnit d) := by
  obtain ⟨g, hg_eq⟩ : ∃ g : K[X], g = EuclideanDomain.gcd p0 (EuclideanDomain.gcd c0 b0) := ⟨_, rfl⟩
  have hg_ne : g ≠ 0 := by
    intro hg0
    rw [hg_eq] at hg0
    have h1 := EuclideanDomain.gcd_eq_zero_iff.mp hg0
    have h2 := EuclideanDomain.gcd_eq_zero_iff.mp h1.2
    rcases hne0 with h | h | h
    · exact h h1.1
    · exact h h2.1
    · exact h h2.2
  have hg_p : g ∣ p0 := by rw [hg_eq]; exact EuclideanDomain.gcd_dvd_left p0 (EuclideanDomain.gcd c0 b0)
  have hg_c : g ∣ c0 := by rw [hg_eq]; exact (EuclideanDomain.gcd_dvd_right p0 (EuclideanDomain.gcd c0 b0)).trans (EuclideanDomain.gcd_dvd_left c0 b0)
  have hg_b : g ∣ b0 := by rw [hg_eq]; exact (EuclideanDomain.gcd_dvd_right p0 (EuclideanDomain.gcd c0 b0)).trans (EuclideanDomain.gcd_dvd_right c0 b0)
  rcases hg_p with ⟨p, hp⟩
  rcases hg_c with ⟨c, hc⟩
  rcases hg_b with ⟨b, hb⟩
  refine ⟨g, p, c, b, hg_ne, hp, hc, hb, ?_, ?_⟩
  · rcases hne0 with h | h | h
    · left; intro hp0; rw [hp0, mul_zero] at hp; exact h hp
    · right; left; intro hc0; rw [hc0, mul_zero] at hc; exact h hc
    · right; right; intro hb0; rw [hb0, mul_zero] at hb; exact h hb
  · intro d hdp hdc hdb
    have hd_all : g * d ∣ g := by
      conv_rhs => rw [hg_eq]
      apply EuclideanDomain.dvd_gcd
      · rw [hp]; exact mul_dvd_mul_left g hdp
      · apply EuclideanDomain.dvd_gcd
        · rw [hc]; exact mul_dvd_mul_left g hdc
        · rw [hb]; exact mul_dvd_mul_left g hdb
    rcases hd_all with ⟨u, hu⟩
    have hdu : d * u = 1 := mul_left_cancel₀ hg_ne (by
      calc g * (d * u) = g * d * u := by ring
        _ = g := hu.symm
        _ = g * 1 := (mul_one g).symm)
    exact isUnit_iff_exists_inv.mpr ⟨u, hdu⟩

private lemma dvd_of_syzygy_coprime_poly {K : Type*} [Field K] [DecidableEq K]
    {p c b N X1 X2 : K[X]} (hp : p ≠ 0)
    (hcop : ∀ d : K[X], d ∣ p → d ∣ c → d ∣ b → IsUnit d)
    (hpc : p * X1 = c * N) (hpb : p * X2 = b * N) : p ∣ N := by
  obtain ⟨g, hg_eq⟩ : ∃ g : K[X], g = EuclideanDomain.gcd p N := ⟨_, rfl⟩
  have hg_ne : g ≠ 0 := fun h0 => hp (EuclideanDomain.gcd_eq_zero_iff.mp (hg_eq ▸ h0)).1
  rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_left p N) with ⟨p', hp'⟩
  rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_right p N) with ⟨N', hN'⟩
  have hp'_cop : IsCoprime p' N' := by
    have hbez : g = p * EuclideanDomain.gcdA p N + N * EuclideanDomain.gcdB p N :=
      hg_eq.trans (EuclideanDomain.gcd_eq_gcd_ab p N)
    refine ⟨EuclideanDomain.gcdA p N, EuclideanDomain.gcdB p N, ?_⟩
    apply mul_left_cancel₀ hg_ne
    calc g * (EuclideanDomain.gcdA p N * p' + EuclideanDomain.gcdB p N * N')
        = (g * p') * EuclideanDomain.gcdA p N + (g * N') * EuclideanDomain.gcdB p N := by ring
      _ = p * EuclideanDomain.gcdA p N + N * EuclideanDomain.gcdB p N := by rw [← hp', ← hN']
      _ = g := hbez.symm
      _ = g * 1 := (mul_one g).symm
  have hp'_c : p' ∣ c := by
    have hd : p' ∣ c * N' := by
      refine ⟨X1, ?_⟩
      apply mul_left_cancel₀ hg_ne
      calc g * (c * N') = c * (g * N') := by ring
        _ = c * N := by rw [← hN']
        _ = p * X1 := hpc.symm
        _ = g * (p' * X1) := by rw [hp']; ring
    exact hp'_cop.dvd_of_dvd_mul_right hd
  have hp'_b : p' ∣ b := by
    have hd : p' ∣ b * N' := by
      refine ⟨X2, ?_⟩
      apply mul_left_cancel₀ hg_ne
      calc g * (b * N') = b * (g * N') := by ring
        _ = b * N := by rw [← hN']
        _ = p * X2 := hpb.symm
        _ = g * (p' * X2) := by rw [hp']; ring
    exact hp'_cop.dvd_of_dvd_mul_right hd
  have hp'_u : IsUnit p' := hcop p' ⟨g, by rw [hp', mul_comm]⟩ hp'_c hp'_b
  obtain ⟨u, hu⟩ := hp'_u
  refine ⟨(u⁻¹ : K[X]ˣ) * N', ?_⟩
  calc N = g * N' := hN'
    _ = g * (↑u * ↑u⁻¹) * N' := by rw [Units.mul_inv, mul_one]
    _ = (g * ↑u) * (↑u⁻¹ * N') := by ring
    _ = p * (↑u⁻¹ * N') := by rw [hu, ← hp']

private lemma dvd_of_sq_dvd_sq_poly {K : Type*} [Field K] [DecidableEq K]
    {a b : K[X]} (h : a ^ 2 ∣ b ^ 2) : a ∣ b := by
  by_cases ha : a = 0
  · subst ha; simp at h; rw [h]
  · obtain ⟨g, hg_eq⟩ : ∃ g : K[X], g = EuclideanDomain.gcd a b := ⟨_, rfl⟩
    have hg_ne : g ≠ 0 := fun h0 => ha (EuclideanDomain.gcd_eq_zero_iff.mp (hg_eq ▸ h0)).1
    rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_left a b) with ⟨a', ha'⟩
    rcases (hg_eq ▸ EuclideanDomain.gcd_dvd_right a b) with ⟨b', hb'⟩
    have hcop : IsCoprime a' b' := by
      have hbez : g = a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b :=
        hg_eq.trans (EuclideanDomain.gcd_eq_gcd_ab a b)
      refine ⟨EuclideanDomain.gcdA a b, EuclideanDomain.gcdB a b, ?_⟩
      apply mul_left_cancel₀ hg_ne
      calc g * (EuclideanDomain.gcdA a b * a' + EuclideanDomain.gcdB a b * b')
          = (g * a') * EuclideanDomain.gcdA a b + (g * b') * EuclideanDomain.gcdB a b := by ring
        _ = a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b := by rw [← ha', ← hb']
        _ = g := hbez.symm
        _ = g * 1 := (mul_one g).symm
    have hd2 : a' ^ 2 ∣ b' ^ 2 := by
      rcases h with ⟨w, hw⟩
      refine ⟨w, mul_left_cancel₀ (pow_ne_zero 2 hg_ne) ?_⟩
      calc g ^ 2 * b' ^ 2 = (g * b') ^ 2 := by ring
        _ = b ^ 2 := by rw [← hb']
        _ = a ^ 2 * w := hw
        _ = (g * a') ^ 2 * w := by rw [ha']
        _ = g ^ 2 * (a' ^ 2 * w) := by ring
    have hu : IsUnit a' := hcop.pow_right.isUnit_of_dvd' dvd_rfl ((dvd_pow_self a' (by norm_num)).trans hd2)
    obtain ⟨u, hu'⟩ := hu
    refine ⟨(u⁻¹ : K[X]ˣ) * b', ?_⟩
    calc b = g * b' := hb'
      _ = g * (↑u * ↑u⁻¹) * b' := by rw [Units.mul_inv, mul_one]
      _ = (g * ↑u) * (↑u⁻¹ * b') := by ring
      _ = a * (↑u⁻¹ * b') := by rw [hu', ← ha']

private lemma syzygy_res_factor_of_inj {K : Type*} [Field K] [CharP K 2]
    (ι : Fld[X] →+* K) (hι : Function.Injective ι)
    (P0 P1 P2 C0 C1 C2 B0 B1 B2 p c b M21 M20 M10 : Fld[X])
    (hp : p ≠ 0) (hg2 : C2.comp (X ^ 2) + X * B2.comp (X ^ 2) ≠ 0)
    (hsyz0 : p * P0 + c * C0 + b * B0 = 0)
    (hsyz1 : p * P1 + c * C1 + b * B1 = 0)
    (hsyz2 : p * P2 + c * C2 + b * B2 = 0)
    (hM21 : p * M21 = C2 * B1 + C1 * B2)
    (hM20 : p * M20 = C2 * B0 + C0 * B2)
    (hM10 : p * M10 = C1 * B0 + C0 * B1) :
    let g0 := C0.comp (X ^ 2) + X * B0.comp (X ^ 2)
    let g1 := C1.comp (X ^ 2) + X * B1.comp (X ^ 2)
    let g2 := C2.comp (X ^ 2) + X * B2.comp (X ^ 2)
    let R := b.comp (X ^ 2) + X * c.comp (X ^ 2)
    let f0 : BiPoly Fld :=
      (C (P0.comp (X ^ 2)) + C (P1.comp (X ^ 2)) * X + C (P2.comp (X ^ 2)) * X ^ 2).comp (X ^ 2) +
      X * (C (B0.comp (X ^ 2)) + C (B1.comp (X ^ 2)) * X + C (B2.comp (X ^ 2)) * X ^ 2).comp (X ^ 2)
    let f1 : BiPoly Fld := (C g0 + C g1 * X + C g2 * X ^ 2).comp (X ^ 2)
    Polynomial.resultant f0 f1 5 4 =
      (p.comp (X ^ 2) ^ 4 * g0 + p.comp (X ^ 2) ^ 2 * R ^ 2 * g1 + R ^ 4 * g2) *
      ((M20 ^ 2 + M21 * M10).comp (X ^ 2)) ^ 2 := by
  intro g0 g1 g2 R f0 f1
  apply hι
  rw [← Polynomial.resultant_map_map]
  have hp_ne : ι (p.comp (X ^ 2)) ≠ 0 := fun h0 =>
    hp ((comp_X_sq_eq_zero_iff p).mp (hι (by rw [map_zero]; exact h0)))
  have hg2_ne : ι (C2.comp (X ^ 2)) + ι X * ι (B2.comp (X ^ 2)) ≠ 0 := by
    intro h0; apply hg2; apply hι
    rw [map_add, map_mul, map_zero]; exact h0
  have hsyz_lift : ∀ Pj Cj Bj : Fld[X], p * Pj + c * Cj + b * Bj = 0 →
      ι (p.comp (X ^ 2)) * ι (Pj.comp (X ^ 2)) + ι (c.comp (X ^ 2)) * ι (Cj.comp (X ^ 2)) +
      ι (b.comp (X ^ 2)) * ι (Bj.comp (X ^ 2)) = 0 := fun Pj Cj Bj h => by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, ← mul_comp, ← mul_comp, ← mul_comp,
      ← add_comp, ← add_comp, h, zero_comp, map_zero]
  have hM_lift : ∀ Ca Ba Cb Bb M : Fld[X], p * M = Ca * Bb + Cb * Ba →
      ι (p.comp (X ^ 2)) * ι (M.comp (X ^ 2)) =
      ι (Ca.comp (X ^ 2)) * ι (Bb.comp (X ^ 2)) + ι (Cb.comp (X ^ 2)) * ι (Ba.comp (X ^ 2)) := fun Ca Ba Cb Bb M hM => by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_add, ← mul_comp, ← mul_comp, ← mul_comp, ← add_comp, hM]
  have hid := char2_resultant_5_4_syzygy_factor
    (ι (P0.comp (X ^ 2))) (ι (P1.comp (X ^ 2))) (ι (P2.comp (X ^ 2)))
    (ι (C0.comp (X ^ 2))) (ι (C1.comp (X ^ 2))) (ι (C2.comp (X ^ 2)))
    (ι (B0.comp (X ^ 2))) (ι (B1.comp (X ^ 2))) (ι (B2.comp (X ^ 2)))
    (ι (p.comp (X ^ 2))) (ι (c.comp (X ^ 2))) (ι (b.comp (X ^ 2))) (ι X)
    (ι (M21.comp (X ^ 2))) (ι (M20.comp (X ^ 2))) (ι (M10.comp (X ^ 2)))
    hp_ne hg2_ne
    (hsyz_lift P0 C0 B0 hsyz0) (hsyz_lift P1 C1 B1 hsyz1) (hsyz_lift P2 C2 B2 hsyz2)
    (hM_lift C2 B2 C1 B1 M21 hM21) (hM_lift C2 B2 C0 B0 M20 hM20) (hM_lift C1 B1 C0 B0 M10 hM10)
  have hf0m : f0.map ι =
      (C (ι (P0.comp (X ^ 2))) + C (ι (P1.comp (X ^ 2))) * X + C (ι (P2.comp (X ^ 2))) * X ^ 2).comp (X ^ 2) +
      X * (C (ι (B0.comp (X ^ 2))) + C (ι (B1.comp (X ^ 2))) * X + C (ι (B2.comp (X ^ 2))) * X ^ 2).comp (X ^ 2) := by
    dsimp only [f0]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_comp, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X]
  have hf1m : f1.map ι =
      (C (ι (C0.comp (X ^ 2)) + ι X * ι (B0.comp (X ^ 2))) +
       C (ι (C1.comp (X ^ 2)) + ι X * ι (B1.comp (X ^ 2))) * X +
       C (ι (C2.comp (X ^ 2)) + ι X * ι (B2.comp (X ^ 2))) * X ^ 2).comp (X ^ 2) := by
    dsimp only [f1, g0, g1, g2]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_comp, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, map_add, map_mul]
  rw [hf0m, hf1m, hid]
  simp only [g0, g1, g2, R, add_comp, mul_comp, pow_comp, map_add, map_mul, map_pow]

private lemma shifted_minor_identities_ring {R : Type*} [CommRing R] [CharP R 2]
    (p c b x y y2 y4 P0 P1 P2 C0 C1 C2 B0 B1 B2 M21 M20 M10 : R)
    (hp21 : p * M21 = C2 * B1 + C1 * B2) (hc21 : c * M21 = P2 * B1 + P1 * B2) (hb21 : b * M21 = P2 * C1 + P1 * C2)
    (hp20 : p * M20 = C2 * B0 + C0 * B2) (hc20 : c * M20 = P2 * B0 + P0 * B2) (hb20 : b * M20 = P2 * C0 + P0 * C2)
    (hp10 : p * M10 = C1 * B0 + C0 * B1) (hc10 : c * M10 = P1 * B0 + P0 * B1) (hb10 : b * M10 = P1 * C0 + P0 * C1) :
    let Bsh0 := B0 + y2 * B1 + y4 * B2
    let A0sh0 := P0 + y2 * P1 + y4 * P2 + y * Bsh0
    let A0sh1 := P1 + y * B1
    let A0sh2 := P2 + y * B2
    let A1sh0 := C0 + y2 * C1 + y4 * C2 + x * Bsh0
    let A1sh1 := C1 + x * B1
    let A1sh2 := C2 + x * B2
    let Ush := b + x * c + y * p
    let M20sh := M20 + y2 * M21
    let M10sh := M10 + y4 * M21
    (p * M21 = A1sh2 * B1 + A1sh1 * B2 ∧
     c * M21 = A0sh2 * B1 + A0sh1 * B2 ∧
     Ush * M21 = A0sh2 * A1sh1 + A0sh1 * A1sh2) ∧
    (p * M20sh = A1sh2 * Bsh0 + A1sh0 * B2 ∧
     c * M20sh = A0sh2 * Bsh0 + A0sh0 * B2 ∧
     Ush * M20sh = A0sh2 * A1sh0 + A0sh0 * A1sh2) ∧
    (p * M10sh = A1sh1 * Bsh0 + A1sh0 * B1 ∧
     c * M10sh = A0sh1 * Bsh0 + A0sh0 * B1 ∧
     Ush * M10sh = A0sh1 * A1sh0 + A0sh0 * A1sh1) := by
  intro Bsh0 A0sh0 A0sh1 A0sh2 A1sh0 A1sh1 A1sh2 Ush M20sh M10sh
  have h2z : ∀ f : R, f + f = 0 := CharTwo.add_self_eq_zero
  dsimp only [Bsh0, A0sh0, A0sh1, A0sh2, A1sh0, A1sh1, A1sh2, Ush, M20sh, M10sh]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · linear_combination hp21 - h2z (x * B2 * B1)
  · linear_combination hc21 - h2z (y * B2 * B1)
  · linear_combination hb21 + x * hc21 + y * hp21 - h2z (x * y * B2 * B1)
  · linear_combination hp20 + y2 * hp21 - h2z (y4 * C2 * B2) - h2z (x * B2 * (B0 + y2 * B1 + y4 * B2))
  · linear_combination hc20 + y2 * hc21 - h2z (y4 * P2 * B2) - h2z (y * B2 * (B0 + y2 * B1 + y4 * B2))
  · linear_combination hb20 + x * hc20 + y * hp20 + y2 * (hb21 + x * hc21 + y * hp21) -
      h2z (y4 * P2 * C2) - h2z (x * y4 * P2 * B2) - h2z (y * y4 * C2 * B2) -
      h2z (x * y * B2 * (B0 + y2 * B1 + y4 * B2))
  · have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
    linear_combination hp10 + y4 * hp21 -
      (y2 * C1 * B1 + x * B1 * (B0 + y2 * B1 + y4 * B2)) * h2
  · have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
    linear_combination hc10 + y4 * hc21 -
      (y2 * P1 * B1 + y * B1 * (B0 + y2 * B1 + y4 * B2)) * h2
  · have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
    linear_combination hb10 + x * hc10 + y * hp10 +
      y4 * (hb21 + x * hc21 + y * hp21) -
      (y2 * P1 * C1 + x * y2 * P1 * B1 + y * y2 * C1 * B1 +
        x * y * B1 * (B0 + y2 * B1 + y4 * B2)) * h2

/-! ### Part 4: `ker(D)` `(d₁ = 4, d₀ ≤ 5)` Data Structure (`KerD45Data`) & Universal Bounds -/

/-- Bundled Table 4 input data for a single specialized `z`:
`F ∈ K_{W_F}(1)` with `W_F < 6 * wY - 1`, `deg_Y(f_1) = 4`, `Res_Y^{(5, 4)}(f_0, f_1) ≠ 0`,
and an agreement polynomial `P` (`deg P ≤ wY`) with `evalContact F P = 0` and `|A_z| ≥ A`. -/
structure KerD45Data where
  W_F : ℕ
  hWF_lo : 5 * wY ≤ W_F + 1
  hWF_hi : W_F + 1 < 6 * wY
  f_coord : KerDIdx wY W_F 1 → Fld
  y : Idx → Fld
  k : Idx → ℕ
  hvan : ∀ i : Idx,
    twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (y i) e.1) (k i)
  P : Fld[X]
  hPdeg : P.natDegree ≤ wY
  Az : Finset Idx
  hAz_card : A ≤ Az.card
  hagree : ∀ i ∈ Az, P.eval (BinaryIRSProfile.domain i) = y i
  hFvan : evalContact (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) P = 0
  hf1_deg : ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1).natDegree = 4
  hRes_ne : Polynomial.resultant
      ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 0)
      ((∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).coeff 1) 5 4 ≠ 0

namespace KerD45Data

variable (D : KerD45Data)

noncomputable def F : ContactPoly Fld :=
  ∑ e : KerDIdx wY D.W_F 1, cC (D.f_coord e) * kerDBasisPoly e.1

noncomputable def f0 : BiPoly Fld := D.F.coeff 0
noncomputable def f1 : BiPoly Fld := D.F.coeff 1
noncomputable def ResY : Fld[X] := Polynomial.resultant D.f0 D.f1 5 4

lemma hwY_pos (_ : KerD45Data) : 0 < wY := by norm_num [wY]

/-- Extracted `P_j(T)` (`j ∈ {0, 1, 2}`): coefficient of `Y^(2j)` in `f0(X, Y)` as a polynomial in `T = X^2`. -/
noncomputable def Pj (j : Fin 3) : Fld[X] :=
  ∑ e : KerDIdx wY D.W_F 1,
    if e.1.1 = 0 ∧ e.1.2.1 = 0 ∧ e.1.2.2.1 = j.val then monomial e.1.2.2.2 (D.f_coord e) else 0

/-- Extracted `C_j(T)` (`j ∈ {0, 1, 2}`): even-`X` part of `Y^(2j)` in `f1(X, Y)`. -/
noncomputable def Cj (j : Fin 3) : Fld[X] :=
  ∑ e : KerDIdx wY D.W_F 1,
    if e.1.1 = 1 ∧ e.1.2.1 = 0 ∧ e.1.2.2.1 = j.val then monomial e.1.2.2.2 (D.f_coord e) else 0

/-- Extracted `B_j(T)` (`j ∈ {0, 1, 2}`): coefficient of `Y^(2j+1)` in `f0` (and odd-`X` part of `Y^(2j)` in `f1`). -/
noncomputable def Bj (j : Fin 3) : Fld[X] :=
  ∑ e : KerDIdx wY D.W_F 1,
    if e.1.1 = 0 ∧ e.1.2.1 = 1 ∧ e.1.2.2.1 = j.val then monomial e.1.2.2.2 (D.f_coord e) else 0

/-- `g_j(X) = C_j(X^2) + X B_j(X^2)` (`j = 0, 1, 2` correspond to `g_0, g_2, g_4`). -/
noncomputable def gj (j : Fin 3) : Fld[X] :=
  (D.Cj j).comp (X ^ 2) + X * (D.Bj j).comp (X ^ 2)

lemma e_b_lt_three (e : KerDIdx wY D.W_F 1) : e.1.2.2.1 < 3 := by
  have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
  have hhi := D.hWF_hi
  have hw : 1 ≤ wY := by norm_num [wY]
  have : 2 * e.1.2.2.1 * wY ≤ D.W_F := by omega
  nlinarith

lemma e_kr_cases (e : KerDIdx wY D.W_F 1) :
    (e.1.1 = 0 ∧ e.1.2.1 = 0) ∨ (e.1.1 = 1 ∧ e.1.2.1 = 0) ∨ (e.1.1 = 0 ∧ e.1.2.1 = 1) := by
  have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
  omega

lemma coeff_Pj (j : Fin 3) (a : ℕ) :
    (D.Pj j).coeff a = ∑ e : KerDIdx wY D.W_F 1,
      if e.1.1 = 0 ∧ e.1.2.1 = 0 ∧ e.1.2.2.1 = j.val ∧ e.1.2.2.2 = a then D.f_coord e else 0 := by
  unfold Pj; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro e _
  split_ifs with h1 h2 <;> simp_all [coeff_monomial]

lemma coeff_Cj (j : Fin 3) (a : ℕ) :
    (D.Cj j).coeff a = ∑ e : KerDIdx wY D.W_F 1,
      if e.1.1 = 1 ∧ e.1.2.1 = 0 ∧ e.1.2.2.1 = j.val ∧ e.1.2.2.2 = a then D.f_coord e else 0 := by
  unfold Cj; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro e _
  split_ifs with h1 h2 <;> simp_all [coeff_monomial]

lemma coeff_Bj (j : Fin 3) (a : ℕ) :
    (D.Bj j).coeff a = ∑ e : KerDIdx wY D.W_F 1,
      if e.1.1 = 0 ∧ e.1.2.1 = 1 ∧ e.1.2.2.1 = j.val ∧ e.1.2.2.2 = a then D.f_coord e else 0 := by
  unfold Bj; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro e _
  split_ifs with h1 h2 <;> simp_all [coeff_monomial]

attribute [irreducible] Pj Cj Bj

lemma two_mul_natDegree_Pj_le (j : Fin 3) : 2 * (D.Pj j).natDegree ≤ D.W_F - 2 * j.val * wY := by
  by_cases h0 : D.Pj j = 0
  · simp [h0]
  · have hnz : (D.Pj j).coeff (D.Pj j).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr h0
    rw [coeff_Pj] at hnz
    obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    split_ifs at he with hc
    · have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      rcases hc with ⟨h1, h2, h3, h4⟩
      rw [h1, h2, h3, h4] at hm
      simp only [zero_mul, zero_add] at hm
      omega
    · exact absurd rfl he

lemma two_mul_natDegree_Cj_le (j : Fin 3) :
    2 * (D.Cj j).natDegree ≤ D.W_F + 1 - (2 * j.val + 1) * wY := by
  by_cases h0 : D.Cj j = 0
  · simp [h0]
  · have hnz : (D.Cj j).coeff (D.Cj j).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr h0
    rw [coeff_Cj] at hnz
    obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    split_ifs at he with hc
    · have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      rcases hc with ⟨h1, h2, h3, h4⟩
      rw [h1, h2, h3, h4] at hm
      have hw : 1 ≤ wY := by norm_num [wY]
      have h1w : 1 ≤ (2 * j.val + 1) * wY := by nlinarith
      have hcost : 1 * (wY - 1) + 0 * wY + 2 * j.val * wY = (2 * j.val + 1) * wY - 1 := by
        zify [hw, h1w]; ring
      omega
    · exact absurd rfl he

lemma two_mul_natDegree_Bj_le (j : Fin 3) :
    2 * (D.Bj j).natDegree ≤ D.W_F - (2 * j.val + 1) * wY := by
  by_cases h0 : D.Bj j = 0
  · simp [h0]
  · have hnz : (D.Bj j).coeff (D.Bj j).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr h0
    rw [coeff_Bj] at hnz
    obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
    split_ifs at he with hc
    · have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      rcases hc with ⟨h1, h2, h3, h4⟩
      rw [h1, h2, h3, h4] at hm
      simp only [zero_mul, zero_add] at hm
      have : 1 * wY + 2 * j.val * wY = (2 * j.val + 1) * wY := by ring
      omega
    · exact absurd rfl he

lemma five_wY_le_of_Bj2_ne_zero (hB2 : D.Bj 2 ≠ 0) : 5 * wY ≤ D.W_F := by
  have hnz : (D.Bj 2).coeff (D.Bj 2).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hB2
  rw [coeff_Bj] at hnz
  obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  split_ifs at he with hc
  · have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
    rcases hc with ⟨h1, h2, h3, h4⟩
    rw [h1, h2, h3, h4] at hm
    simp only [Fin.val_two, zero_mul, zero_add] at hm
    omega
  · exact absurd rfl he

lemma natDegree_gj_le (j : Fin 3) :
    (D.gj j).natDegree ≤ D.W_F + 1 - (2 * j.val + 1) * wY := by
  have h1 := D.two_mul_natDegree_Cj_le j
  have h2 := D.two_mul_natDegree_Bj_le j
  have h3 := natDegree_even_odd_le (D.Cj j) (D.Bj j)
  change (D.gj j).natDegree ≤ _ at h3
  have hle : (2 * j.val + 1) * wY ≤ D.W_F + 1 := by
    have := D.hWF_lo; have := j.isLt; nlinarith
  by_cases hB : D.Bj j = 0
  · simp only [hB, ↓reduceIte] at h3; omega
  · simp only [hB, ↓reduceIte] at h3
    have hleB : (2 * j.val + 1) * wY ≤ D.W_F := by
      have hnz : (D.Bj j).coeff (D.Bj j).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hB
      rw [coeff_Bj] at hnz
      obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
      split_ifs at he with hc
      · have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
        rcases hc with ⟨h1, h2, h3, h4⟩
        rw [h1, h2, h3, h4] at hm
        simp only [zero_mul, zero_add] at hm
        have : 1 * wY + 2 * j.val * wY = (2 * j.val + 1) * wY := by ring
        omega
      · exact absurd rfl he
    omega

lemma f0_eq_sum :
    D.f0 = ∑ j : Fin 3, (C ((D.Pj j).comp (X ^ 2)) * X ^ (2 * j.val) +
      C ((D.Bj j).comp (X ^ 2)) * X ^ (2 * j.val + 1)) := by
  apply Polynomial.ext; intro m
  apply Polynomial.ext; intro i
  have hL : (D.f0.coeff m).coeff i = ((D.F.coeff 0).coeff m).coeff i := rfl
  rw [hL, show D.F = ∑ e : KerDIdx wY D.W_F 1, cC (D.f_coord e) * kerDBasisPoly e.1 from rfl,
    coeff_sum_kerDBasisPoly D.hwY_pos]
  rw [finset_sum_coeff, finset_sum_coeff]
  simp_rw [coeff_add, coeff_C_mul_X_pow]
  by_cases h00 : m % 2 = 0 ∧ i % 2 = 0
  · simp only [h00, and_self, ↓reduceIte]
    have hRHS : (∑ j : Fin 3, ((if m = 2 * j.val then (D.Pj j).comp (X ^ 2) else 0).coeff i +
        (if m = 2 * j.val + 1 then (D.Bj j).comp (X ^ 2) else 0).coeff i)) =
        if hm3 : m / 2 < 3 then (D.Pj ⟨m / 2, hm3⟩).coeff (i / 2) else 0 := by
      by_cases hm3 : m / 2 < 3
      · rw [dif_pos hm3, Finset.sum_eq_single ⟨m / 2, hm3⟩]
        · have hm2 : m = 2 * (⟨m / 2, hm3⟩ : Fin 3).val := by dsimp; omega
          have hmne : m ≠ 2 * (⟨m / 2, hm3⟩ : Fin 3).val + 1 := by dsimp; omega
          rw [if_pos hm2, if_neg hmne, coeff_zero, add_zero]
          have hi2 : i = 2 * (i / 2) := by omega
          conv_lhs => rw [hi2]
          rw [comp_X_sq_coeff_even]
        · intro j _ hne
          have h1 : m ≠ 2 * j.val := by intro h; apply hne; ext; dsimp; have := h00.1; omega
          have h2 : m ≠ 2 * j.val + 1 := by have := h00.1; omega
          rw [if_neg h1, if_neg h2, coeff_zero, add_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [dif_neg hm3]; apply Finset.sum_eq_zero; intro j _
        have h1 : m ≠ 2 * j.val := by have := j.isLt; omega
        have h2 : m ≠ 2 * j.val + 1 := by have := h00.1; omega
        rw [if_neg h1, if_neg h2, coeff_zero, add_zero]
    rw [hRHS]
    split_ifs with hmem hm3
    · rw [coeff_Pj, Finset.sum_eq_single ⟨(0, 0, m / 2, i / 2), hmem⟩]
      · simp
      · intro e _ hne
        split_ifs with hc
        · exfalso; apply hne; apply Subtype.ext
          rcases e with ⟨⟨k1, r1, b1, a1⟩, _⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; rfl
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    · exfalso; exact hm3 (D.e_b_lt_three ⟨(0, 0, m / 2, i / 2), hmem⟩)
    · rw [coeff_Pj]; symm; apply Finset.sum_eq_zero; intro e _
      split_ifs with hc
      · exfalso; apply hmem
        rcases e with ⟨⟨k1, r1, b1, a1⟩, he⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; exact he
      · rfl
    · rfl
  · simp only [h00, ↓reduceIte]
    by_cases h10 : m % 2 = 1 ∧ i % 2 = 0
    · simp only [h10, and_self, ↓reduceIte]
      have hRHS : (∑ j : Fin 3, ((if m = 2 * j.val then (D.Pj j).comp (X ^ 2) else 0).coeff i +
          (if m = 2 * j.val + 1 then (D.Bj j).comp (X ^ 2) else 0).coeff i)) =
          if hm3 : m / 2 < 3 then (D.Bj ⟨m / 2, hm3⟩).coeff (i / 2) else 0 := by
        by_cases hm3 : m / 2 < 3
        · rw [dif_pos hm3, Finset.sum_eq_single ⟨m / 2, hm3⟩]
          · have hm2 : m = 2 * (⟨m / 2, hm3⟩ : Fin 3).val + 1 := by dsimp; omega
            have hmne : m ≠ 2 * (⟨m / 2, hm3⟩ : Fin 3).val := by dsimp; omega
            rw [if_neg hmne, if_pos hm2, coeff_zero, zero_add]
            have hi2 : i = 2 * (i / 2) := by omega
            conv_lhs => rw [hi2]
            rw [comp_X_sq_coeff_even]
          · intro j _ hne
            have h1 : m ≠ 2 * j.val := by have := h10.1; omega
            have h2 : m ≠ 2 * j.val + 1 := by intro h; apply hne; ext; dsimp; have := h10.1; omega
            rw [if_neg h1, if_neg h2, coeff_zero, add_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [dif_neg hm3]; apply Finset.sum_eq_zero; intro j _
          have h1 : m ≠ 2 * j.val := by have := h10.1; omega
          have h2 : m ≠ 2 * j.val + 1 := by have := j.isLt; omega
          rw [if_neg h1, if_neg h2, coeff_zero, add_zero]
      rw [hRHS]
      split_ifs with hmem hm3
      · rw [coeff_Bj, Finset.sum_eq_single ⟨(0, 1, m / 2, i / 2), hmem⟩]
        · simp
        · intro e _ hne
          split_ifs with hc
          · exfalso; apply hne; apply Subtype.ext
            rcases e with ⟨⟨k1, r1, b1, a1⟩, _⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; rfl
          · rfl
        · intro h; exact absurd (Finset.mem_univ _) h
      · exfalso; exact hm3 (D.e_b_lt_three ⟨(0, 1, m / 2, i / 2), hmem⟩)
      · rw [coeff_Bj]; symm; apply Finset.sum_eq_zero; intro e _
        split_ifs with hc
        · exfalso; apply hmem
          rcases e with ⟨⟨k1, r1, b1, a1⟩, he⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; exact he
        · rfl
      · rfl
    · simp only [h10, ↓reduceIte]
      have hi_odd : i % 2 = 1 := by omega
      have h0_lt : ¬ (0 < (0 : ℕ)) := by omega
      simp only [h0_lt, and_false, ↓reduceIte]
      symm; apply Finset.sum_eq_zero; intro j _
      have hA : (if m = 2 * j.val then (D.Pj j).comp (X ^ 2) else 0).coeff i = 0 := by
        split_ifs
        · rw [show i = 2 * (i / 2) + 1 by omega, comp_X_sq_coeff_odd]
        · simp
      have hB : (if m = 2 * j.val + 1 then (D.Bj j).comp (X ^ 2) else 0).coeff i = 0 := by
        split_ifs
        · rw [show i = 2 * (i / 2) + 1 by omega, comp_X_sq_coeff_odd]
        · simp
      rw [hA, hB, add_zero]

lemma f1_eq_sum : D.f1 = ∑ j : Fin 3, C (D.gj j) * X ^ (2 * j.val) := by
  apply Polynomial.ext; intro m
  apply Polynomial.ext; intro i
  have hL : (D.f1.coeff m).coeff i = ((D.F.coeff 1).coeff m).coeff i := rfl
  rw [hL, show D.F = ∑ e : KerDIdx wY D.W_F 1, cC (D.f_coord e) * kerDBasisPoly e.1 from rfl,
    coeff_sum_kerDBasisPoly D.hwY_pos]
  rw [finset_sum_coeff, finset_sum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  have hRHS : (∑ j : Fin 3, (if m = 2 * j.val then D.gj j else 0).coeff i) =
      if hm : m % 2 = 0 ∧ m / 2 < 3 then
        (if i % 2 = 0 then (D.Cj ⟨m / 2, hm.2⟩).coeff (i / 2) else (D.Bj ⟨m / 2, hm.2⟩).coeff (i / 2))
      else 0 := by
    by_cases hm : m % 2 = 0 ∧ m / 2 < 3
    · rw [dif_pos hm, Finset.sum_eq_single ⟨m / 2, hm.2⟩]
      · have hm2 : m = 2 * (⟨m / 2, hm.2⟩ : Fin 3).val := by dsimp; omega
        rw [if_pos hm2]
        exact coeff_even_odd_pair (D.Cj ⟨m / 2, hm.2⟩) (D.Bj ⟨m / 2, hm.2⟩) i
      · intro j _ hne
        have h1 : m ≠ 2 * j.val := by intro h; apply hne; ext; dsimp; have := hm.1; omega
        rw [if_neg h1, coeff_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg hm]; apply Finset.sum_eq_zero; intro j _
      have h1 : m ≠ 2 * j.val := by have := j.isLt; omega
      rw [if_neg h1, coeff_zero]
  rw [hRHS]
  by_cases h00 : m % 2 = 0 ∧ i % 2 = 0
  · simp only [h00, and_self, ↓reduceIte]
    split_ifs with hmem hm
    · rw [coeff_Cj, Finset.sum_eq_single ⟨(1, 0, m / 2, i / 2), hmem⟩]
      · simp
      · intro e _ hne
        split_ifs with hc
        · exfalso; apply hne; apply Subtype.ext
          rcases e with ⟨⟨k1, r1, b1, a1⟩, _⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; rfl
        · rfl
      · intro h; exact absurd (Finset.mem_univ _) h
    · exfalso; exact hm ⟨trivial, D.e_b_lt_three ⟨(1, 0, m / 2, i / 2), hmem⟩⟩
    · rw [coeff_Cj]; symm; apply Finset.sum_eq_zero; intro e _
      split_ifs with hc
      · exfalso; apply hmem
        rcases e with ⟨⟨k1, r1, b1, a1⟩, he⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; exact he
      · rfl
    · rfl
  · simp only [h00, ↓reduceIte]
    by_cases h10 : m % 2 = 1 ∧ i % 2 = 0
    · have hnotm : ¬ (m % 2 = 0 ∧ m / 2 < 3) := by omega
      rw [dif_neg hnotm]
      simp only [h10, and_self, ↓reduceIte]
      split_ifs with hmem
      · exfalso
        have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos 1 1 (m / 2) (i / 2)).mp hmem
        omega
      · rfl
    · simp only [h10, ↓reduceIte]
      by_cases h01 : m % 2 = 0 ∧ i % 2 = 1 ∧ 0 < (1 : ℕ)
      · have hi0 : i % 2 ≠ 0 := by omega
        have hif_rhs : (if hm : m % 2 = 0 ∧ m / 2 < 3 then
            (if i % 2 = 0 then (D.Cj ⟨m / 2, hm.2⟩).coeff (i / 2) else (D.Bj ⟨m / 2, hm.2⟩).coeff (i / 2))
            else 0) = if hm : m % 2 = 0 ∧ m / 2 < 3 then (D.Bj ⟨m / 2, hm.2⟩).coeff (i / 2) else 0 := by
          split_ifs <;> first | exact absurd ‹_› hi0 | rfl
        rw [hif_rhs]
        simp only [h01, and_self, ↓reduceIte, Nat.sub_self]
        split_ifs with hmem hm
        · rw [coeff_Bj, Finset.sum_eq_single ⟨(0, 1, m / 2, i / 2), hmem⟩]
          · simp
          · intro e _ hne
            split_ifs with hc
            · exfalso; apply hne; apply Subtype.ext
              rcases e with ⟨⟨k1, r1, b1, a1⟩, _⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; rfl
            · rfl
          · intro h; exact absurd (Finset.mem_univ _) h
        · exfalso; exact hm ⟨trivial, D.e_b_lt_three ⟨(0, 1, m / 2, i / 2), hmem⟩⟩
        · rw [coeff_Bj]; symm; apply Finset.sum_eq_zero; intro e _
          split_ifs with hc
          · exfalso; apply hmem
            rcases e with ⟨⟨k1, r1, b1, a1⟩, he⟩; simp at hc; rcases hc with ⟨rfl, rfl, rfl, rfl⟩; exact he
          · rfl
        · rfl
      · have hnotm : ¬ (m % 2 = 0 ∧ m / 2 < 3) := by omega
        rw [dif_neg hnotm]
        simp only [h01, ↓reduceIte]

lemma f0_coeff_even (j : Fin 3) : D.f0.coeff (2 * j.val) = (D.Pj j).comp (X ^ 2) := by
  rw [D.f0_eq_sum, finset_sum_coeff, Finset.sum_eq_single j]
  · rw [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, if_pos rfl, if_neg (by omega), add_zero]
  · intro m _ hne
    have h1 : 2 * j.val ≠ 2 * m.val := by intro h; apply hne; ext; omega
    have h2 : 2 * j.val ≠ 2 * m.val + 1 := by omega
    rw [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, if_neg h1, if_neg h2, add_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma f0_coeff_odd (j : Fin 3) : D.f0.coeff (2 * j.val + 1) = (D.Bj j).comp (X ^ 2) := by
  rw [D.f0_eq_sum, finset_sum_coeff, Finset.sum_eq_single j]
  · rw [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, if_neg (by omega), if_pos rfl, zero_add]
  · intro m _ hne
    have h1 : 2 * j.val + 1 ≠ 2 * m.val := by omega
    have h2 : 2 * j.val + 1 ≠ 2 * m.val + 1 := by intro h; apply hne; ext; omega
    rw [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, if_neg h1, if_neg h2, add_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma f1_coeff_even (j : Fin 3) : D.f1.coeff (2 * j.val) = D.gj j := by
  rw [D.f1_eq_sum, finset_sum_coeff, Finset.sum_eq_single j]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro m _ hne
    have h1 : 2 * j.val ≠ 2 * m.val := by intro h; apply hne; ext; omega
    rw [coeff_C_mul_X_pow, if_neg h1]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma f1_coeff_odd (m : ℕ) (hm : m % 2 = 1) : D.f1.coeff m = 0 := by
  rw [D.f1_eq_sum, finset_sum_coeff]
  apply Finset.sum_eq_zero; intro j _
  rw [coeff_C_mul_X_pow, if_neg (by omega)]

lemma f0_natDegree_le : D.f0.natDegree ≤ 5 := by
  rw [D.f0_eq_sum]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
  dsimp only [Function.comp_apply]
  have hj := j.isLt
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _ |>.trans (by omega))
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _ |>.trans (by omega))

lemma f1_natDegree_eq : D.f1.natDegree = 4 := D.hf1_deg

lemma g2_ne_zero : D.gj 2 ≠ 0 := by
  have h4 := D.f1_coeff_even 2
  change D.f1.coeff 4 = D.gj 2 at h4
  rw [← h4, ← D.f1_natDegree_eq]
  exact leadingCoeff_ne_zero.mpr (by intro h0; have hd := D.f1_natDegree_eq; rw [h0, natDegree_zero] at hd; omega)

lemma f1_eval_P_ne_zero : D.f1.eval D.P ≠ 0 := by
  intro hf10
  have hF0 : D.f0.eval D.P + D.P.derivative * D.f1.eval D.P = 0 := by
    have hFdeg : D.F.natDegree ≤ 1 := by
      unfold F
      refine (natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => ?_)
      dsimp only [Function.comp_apply]
      have hm := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      refine natDegree_mul_le.trans ?_
      have h1 : (cC (D.f_coord e)).natDegree = 0 := by unfold cC; simp
      have h2 : (kerDBasisPoly (A := Fld) e.1).natDegree ≤ e.1.1 + e.1.2.1 := by
        unfold kerDBasisPoly cR cY cX
        refine natDegree_mul_le.trans ?_
        have hb : ((C X ^ 2 : ContactPoly Fld) ^ e.1.2.2.1).natDegree = 0 := by
          rw [← map_pow, ← map_pow, natDegree_C]
        rw [hb, add_zero]
        refine natDegree_mul_le.trans ?_
        have ha : ((C (C X) ^ 2 : ContactPoly Fld) ^ e.1.2.2.2).natDegree = 0 := by
          rw [← map_pow, ← map_pow, natDegree_C]
        rw [ha, add_zero]
        refine natDegree_mul_le.trans (Nat.add_le_add (natDegree_X_pow_le _) ?_)
        refine natDegree_pow_le.trans ?_
        have hlin : (C X + C (C X) * X : ContactPoly Fld).natDegree ≤ 1 :=
          (natDegree_add_le _ _).trans (max_le (by simp) (natDegree_mul_le.trans (by simp)))
        nlinarith
      omega
    have hFexp : D.F = C D.f0 + C D.f1 * X := by
      apply Polynomial.ext; intro m; cases m with
      | zero => simp [f0, f1]
      | succ m' => cases m' with
        | zero => simp [f0, f1]
        | succ m'' =>
            rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hFdeg (by omega))]
            simp [coeff_C, coeff_mul_X]
    have hv := D.hFvan
    change evalContact D.F D.P = 0 at hv
    rw [hFexp] at hv
    simp only [evalContact, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      eval_add, eval_mul, eval_C, eval_X, Polynomial.coe_evalRingHom] at hv
    simpa [mul_comm] using hv
  rw [hf10, mul_zero, add_zero] at hF0
  let ι : Fld[X] →+* RatFunc Fld := algebraMap Fld[X] (RatFunc Fld)
  have hRes0' : ι D.ResY = 0 := by
    unfold ResY; rw [← Polynomial.resultant_map_map]
    exact P64Resultant.fixed_resultant_eq_zero_of_common_root
      (natDegree_map_le.trans D.f0_natDegree_le)
      (natDegree_map_le.trans (le_of_eq D.f1_natDegree_eq))
      (by omega)
      (by rw [Polynomial.eval_map_apply, hF0, map_zero])
      (by rw [Polynomial.eval_map_apply, hf10, map_zero])
  exact D.hRes_ne (IsFractionRing.injective Fld[X] (RatFunc Fld) (by change ι D.ResY = ι 0; rw [hRes0', map_zero]))

lemma ResY_ne_zero : D.ResY ≠ 0 := D.hRes_ne

lemma local_biMult_f0_f1 (i : Idx) :
    biMultGE (BinaryIRSProfile.domain i) (D.y i) D.f0 (2 * D.k i - 1) ∧
    biMultGE (BinaryIRSProfile.domain i) (D.y i) D.f1 (2 * D.k i - 1) :=
  kerD1_local_ords D.hwY_pos (BinaryIRSProfile.domain i) (D.y i) D.f_coord (D.hvan i)

attribute [irreducible] F f0 f1

lemma natDegree_f1_eval_P_le : (D.f1.eval D.P).natDegree ≤ D.W_F - wY + 1 := by
  have hev_sum : D.f1.eval D.P = ∑ j : Fin 3, (C (D.gj j) * X ^ (2 * j.val)).eval D.P := by
    rw [D.f1_eq_sum]; exact map_sum (Polynomial.evalRingHom D.P) _ _
  rw [hev_sum]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
  dsimp only [Function.comp_apply]
  rw [eval_mul, eval_C, eval_pow, eval_X]
  have hmul : (D.gj j * D.P ^ (2 * j.val)).natDegree ≤ (D.gj j).natDegree + (D.P ^ (2 * j.val)).natDegree :=
    natDegree_mul_le
  have hpow : (D.P ^ (2 * j.val)).natDegree ≤ (2 * j.val) * D.P.natDegree := natDegree_pow_le
  have hgj := D.natDegree_gj_le j
  have := D.hPdeg; have := D.hWF_lo; have := j.isLt
  have : (2 * j.val + 1) * wY = 2 * j.val * wY + wY := by ring
  have h1 : 2 * j.val * D.P.natDegree ≤ 2 * j.val * wY := Nat.mul_le_mul_left _ D.hPdeg
  have h5 : (2 * j.val + 1) * wY ≤ 5 * wY := Nat.mul_le_mul_right wY (by omega)
  have hw1 : 1 ≤ wY := by norm_num [wY]
  omega

/-- **Universal Sylvester Col-1 Degree Bound (`Res_Y^{(5, 4)}`):**
`deg_X(Res_Y) ≤ 8 W_F - 20 wY + 4 + deg_X(g_4)`. -/
theorem natDegree_ResY_le_col1 :
    D.ResY.natDegree ≤ 8 * D.W_F - 20 * wY + 4 + (D.gj 2).natDegree := by
  classical
  have hWF5 : 5 * wY ≤ D.W_F + 1 := D.hWF_lo
  -- Degree bound for every nonzero entry of f0 and f1!
  have hf0_deg : ∀ m, D.f0.coeff m ≠ 0 → (D.f0.coeff m).natDegree + m * wY ≤ D.W_F := by
    intro m hm
    have hm6 : m < 6 := by
      by_contra h; exact hm (coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt D.f0_natDegree_le (by omega)))
    have hcase : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
    · have := D.f0_coeff_even 0; simp at this; rw [this, natDegree_comp_X_sq]
      have := D.two_mul_natDegree_Pj_le 0; simp at this; omega
    · have := D.f0_coeff_odd 0; simp at this; rw [this, natDegree_comp_X_sq]
      have := D.two_mul_natDegree_Bj_le 0; simp at this
      have : wY ≤ D.W_F := by have := D.hWF_lo; have := D.hwY_pos; omega
      omega
    · have := D.f0_coeff_even 1; simp at this; rw [this, natDegree_comp_X_sq]
      have := D.two_mul_natDegree_Pj_le 1; simp at this
      have : 2 * wY ≤ D.W_F := by have := D.hWF_lo; have := D.hwY_pos; omega
      omega
    · have := D.f0_coeff_odd 1; simp at this; rw [this, natDegree_comp_X_sq]
      have := D.two_mul_natDegree_Bj_le 1; simp at this
      have : 3 * wY ≤ D.W_F := by have := D.hWF_lo; have := D.hwY_pos; omega
      omega
    · have := D.f0_coeff_even 2; simp at this; rw [this, natDegree_comp_X_sq]
      have := D.two_mul_natDegree_Pj_le 2; simp at this
      have : 4 * wY ≤ D.W_F := by have := D.hWF_lo; have := D.hwY_pos; omega
      omega
    · have := D.f0_coeff_odd 2; simp at this; rw [this, natDegree_comp_X_sq]
      have hB2 : D.Bj 2 ≠ 0 := by rw [this] at hm; exact mt (comp_X_sq_eq_zero_iff _).mpr hm
      have hnz : (D.Bj 2).coeff (D.Bj 2).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hB2
      rw [coeff_Bj] at hnz
      obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
      split_ifs at he with hc
      · have hmem := (mem_kerDIdxFinset_iff wY D.W_F 1 D.hwY_pos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
        rcases hc with ⟨h1, h2, h3, h4⟩
        rw [h1, h2, h3, h4] at hmem
        simp only [Fin.val_two, zero_mul, zero_add, one_mul] at hmem
        omega
      · exact absurd rfl he
  have hf1_deg : ∀ m, D.f1.coeff m ≠ 0 → (D.f1.coeff m).natDegree + (m + 1) * wY ≤ D.W_F + 1 := by
    intro m hm
    have hm5 : m < 5 := by
      by_contra h; exact hm (coeff_eq_zero_of_natDegree_lt (by rw [D.f1_natDegree_eq]; omega))
    have hcase : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl
    · have := D.f1_coeff_even 0; simp at this; rw [this]; have := D.natDegree_gj_le 0; simp at this; omega
    · exact absurd (D.f1_coeff_odd 1 rfl) hm
    · have := D.f1_coeff_even 1; simp at this; rw [this]; have := D.natDegree_gj_le 1; simp at this; omega
    · exact absurd (D.f1_coeff_odd 3 rfl) hm
    · have := D.f1_coeff_even 2; simp at this; rw [this]; have := D.natDegree_gj_le 2; simp at this; omega
  -- Key row-8 bound: f1.coeff 4 = g2 (deg = g2.natDegree), f0.coeff 5 = B2(X^2) (deg + 1 ≤ g2.natDegree if ≠ 0)!
  have hB2_le_g2 : D.f0.coeff 5 ≠ 0 → (D.f0.coeff 5).natDegree + 1 ≤ (D.gj 2).natDegree := by
    intro h5
    have h5eq : D.f0.coeff 5 = (D.Bj 2).comp (X ^ 2) := D.f0_coeff_odd 2
    rw [h5eq] at h5 ⊢
    have hBne : D.Bj 2 ≠ 0 := mt (comp_X_sq_eq_zero_iff _).mpr h5
    rw [natDegree_comp_X_sq]
    exact two_mul_natDegree_add_one_le_even_odd (D.Cj 2) (D.Bj 2) hBne
  unfold ResY; rw [Polynomial.resultant, Matrix.det_apply]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
  dsimp only [Function.comp_apply]
  have hzsmul : ∀ (u : ℤˣ) (p : Fld[X]), (u • p).natDegree ≤ p.natDegree := fun u p => by
    rw [Units.smul_def]; rcases Int.units_eq_one_or u with rfl | rfl <;> simp
  refine (hzsmul _ _).trans ?_
  by_cases hzero : ∃ j : Fin 9, Polynomial.sylvester D.f0 D.f1 5 4 (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    rw [Finset.prod_eq_zero (f := fun i => Polynomial.sylvester D.f0 D.f1 5 4 (σ i) i) (Finset.mem_univ j) hj,
      natDegree_zero]; exact Nat.zero_le _
  · push Not at hzero
    let jr : Fin 5 → ℕ := fun r' => (σ (Fin.castAdd 4 r')).val - r'.val
    let ir : Fin 4 → ℕ := fun r => (σ (Fin.natAdd 5 r)).val - r.val
    have hbounds :
      (∀ r' : Fin 5, r'.val ≤ (σ (Fin.castAdd 4 r')).val ∧
        (σ (Fin.castAdd 4 r')).val ≤ r'.val + 4 ∧
        Polynomial.sylvester D.f0 D.f1 5 4 (σ (Fin.castAdd 4 r')) (Fin.castAdd 4 r') = D.f1.coeff (jr r')) ∧
      (∀ r : Fin 4, r.val ≤ (σ (Fin.natAdd 5 r)).val ∧
        (σ (Fin.natAdd 5 r)).val ≤ r.val + 5 ∧
        Polynomial.sylvester D.f0 D.f1 5 4 (σ (Fin.natAdd 5 r)) (Fin.natAdd 5 r) = D.f0.coeff (ir r)) := by
      constructor
      · intro r'; have hne := hzero (Fin.castAdd 4 r')
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
      · intro r; have hne := hzero (Fin.natAdd 5 r)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc
        · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
    have hsum : (∑ r : Fin 4, ir r) + (∑ r' : Fin 5, jr r') = 20 := by
      have hperm := Equiv.sum_comp σ (fun k : Fin 9 => k.val)
      have hsp1 : ∑ k : Fin (5 + 4), (σ k).val =
          (∑ r' : Fin 5, (σ (Fin.castAdd 4 r')).val) + (∑ r : Fin 4, (σ (Fin.natAdd 5 r)).val) :=
        Fin.sum_univ_add (fun k : Fin (5 + 4) => (σ k).val)
      have hsp2 : ∑ k : Fin (5 + 4), k.val =
          (∑ r' : Fin 5, r'.val) + (∑ r : Fin 4, (5 + r.val)) := by
        rw [Fin.sum_univ_add (fun k : Fin (5 + 4) => k.val)]; rfl
      have hG : (∑ r' : Fin 5, jr r') + (∑ r' : Fin 5, r'.val) = ∑ r' : Fin 5, (σ (Fin.castAdd 4 r')).val := by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r' _
        have := (hbounds.1 r').1; dsimp [jr]; omega
      have hF : (∑ r : Fin 4, ir r) + (∑ r : Fin 4, r.val) = ∑ r : Fin 4, (σ (Fin.natAdd 5 r)).val := by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r _
        have := (hbounds.2 r).1; dsimp [ir]; omega
      have h5 : ∑ r : Fin 4, (5 + r.val) = 20 + ∑ r : Fin 4, r.val := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp
      omega
    have hprod_deg : (∏ j : Fin (5 + 4), Polynomial.sylvester D.f0 D.f1 5 4 (σ j) j).natDegree ≤
        (∑ r' : Fin 5, (D.f1.coeff (jr r')).natDegree) + (∑ r : Fin 4, (D.f0.coeff (ir r)).natDegree) := by
      rw [Fin.prod_univ_add (f := fun j : Fin (5 + 4) => Polynomial.sylvester D.f0 D.f1 5 4 (σ j) j)]
      refine natDegree_mul_le.trans (Nat.add_le_add ?_ ?_)
      · refine (natDegree_prod_le _ _).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl; intro r' _; rw [(hbounds.1 r').2.2]
      · refine (natDegree_prod_le _ _).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl; intro r _; rw [(hbounds.2 r).2.2]
    -- Find j8 = σ⁻¹(8): MUST be either castAdd 4 4 (jr 4 = 4) or natAdd 5 3 (ir 3 = 5)!
    let j8 : Fin (5 + 4) := σ.symm ⟨8, by omega⟩
    have hj8_val : (σ j8).val = 8 := by simp [j8]
    have h8_cases : j8 = Fin.castAdd 4 ⟨4, by omega⟩ ∨ j8 = Fin.natAdd 5 ⟨3, by omega⟩ := by
      generalize hj8_def : j8 = k at hj8_val
      induction k using Fin.addCases with
      | left r' =>
          left; congr 1; ext; dsimp only
          have h2 := (hbounds.1 r').2.1; rw [hj8_val] at h2; have := r'.isLt; omega
      | right r =>
          right; congr 1; ext; dsimp only
          have h2 := (hbounds.2 r).2.1; rw [hj8_val] at h2; have := r.isLt; omega
    have hne_f1 : ∀ r' : Fin 5, D.f1.coeff (jr r') ≠ 0 := fun r' => by
      rw [← (hbounds.1 r').2.2]; exact hzero (Fin.castAdd 4 r')
    have hne_f0 : ∀ r : Fin 4, D.f0.coeff (ir r) ≠ 0 := fun r => by
      rw [← (hbounds.2 r).2.2]; exact hzero (Fin.natAdd 5 r)
    rcases h8_cases with hj8L | hj8R
    · -- Case 1: jr 4 = 4 (entry is g2)!
      have hjr4 : jr ⟨4, by omega⟩ = 4 := by
        show (σ (Fin.castAdd 4 ⟨4, by omega⟩)).val - 4 = 4
        rw [← hj8L, hj8_val]
      have hg2_entry : (D.f1.coeff (jr ⟨4, by omega⟩)).natDegree = (D.gj 2).natDegree := by
        have h4 : D.f1.coeff 4 = D.gj 2 := D.f1_coeff_even 2
        rw [hjr4, h4]
      have hS1 : (∑ r' ∈ Finset.univ.erase (⟨4, by omega⟩ : Fin 5), ((D.f1.coeff (jr r')).natDegree + (jr r' + 1) * wY)) ≤
          4 * (D.W_F + 1) := by
        calc _ ≤ ∑ _r' ∈ Finset.univ.erase (⟨4, by omega⟩ : Fin 5), (D.W_F + 1) :=
              Finset.sum_le_sum fun r' _ => hf1_deg (jr r') (hne_f1 r')
          _ = 4 * (D.W_F + 1) := by simp
      have hS0 : (∑ r : Fin 4, ((D.f0.coeff (ir r)).natDegree + ir r * wY)) ≤ 4 * D.W_F := by
        calc _ ≤ ∑ _r : Fin 4, D.W_F := Finset.sum_le_sum fun r _ => hf0_deg (ir r) (hne_f0 r)
          _ = 4 * D.W_F := by simp
      rw [Finset.sum_add_distrib] at hS1 hS0
      have hsum_er1 : ∑ r' : Fin 5, (D.f1.coeff (jr r')).natDegree =
          (D.gj 2).natDegree + ∑ r' ∈ Finset.univ.erase (⟨4, by omega⟩ : Fin 5), (D.f1.coeff (jr r')).natDegree := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨4, by omega⟩ : Fin 5)), hg2_entry]
      have hsum_jr_er : ∑ r' ∈ Finset.univ.erase (⟨4, by omega⟩ : Fin 5), (jr r' + 1) * wY =
          ((∑ r' : Fin 5, jr r') - 4 + 4) * wY := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        have htot : ∑ r' : Fin 5, jr r' = 4 + ∑ r' ∈ Finset.univ.erase (⟨4, by omega⟩ : Fin 5), jr r' := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨4, by omega⟩ : Fin 5)), hjr4]
        congr 1; omega
      rw [← Finset.sum_mul] at hS0
      have htot_w : ((∑ r' : Fin 5, jr r') - 4 + 4) * wY + (∑ r : Fin 4, ir r) * wY = 20 * wY := by
        have h4le : 4 ≤ ∑ r' : Fin 5, jr r' := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨4, by omega⟩ : Fin 5)), hjr4]; omega
        rw [← Nat.add_mul]; congr 1; omega
      omega
    · -- Case 2: ir 3 = 5 (entry is f0.coeff 5 = B2(X^2), deg + 1 ≤ g2.natDegree)!
      have hir3 : ir ⟨3, by omega⟩ = 5 := by
        show (σ (Fin.natAdd 5 ⟨3, by omega⟩)).val - 3 = 5
        rw [← hj8R, hj8_val]
      have hB2_entry : (D.f0.coeff (ir ⟨3, by omega⟩)).natDegree + 1 ≤ (D.gj 2).natDegree := by
        rw [hir3]; exact hB2_le_g2 (by rw [← hir3]; exact hne_f0 ⟨3, by omega⟩)
      have hS1 : (∑ r' : Fin 5, ((D.f1.coeff (jr r')).natDegree + (jr r' + 1) * wY)) ≤ 5 * (D.W_F + 1) := by
        calc _ ≤ ∑ _r' : Fin 5, (D.W_F + 1) := Finset.sum_le_sum fun r' _ => hf1_deg (jr r') (hne_f1 r')
          _ = 5 * (D.W_F + 1) := by simp
      have hS0 : (∑ r ∈ Finset.univ.erase (⟨3, by omega⟩ : Fin 4), ((D.f0.coeff (ir r)).natDegree + ir r * wY)) ≤
          3 * D.W_F := by
        calc _ ≤ ∑ _r ∈ Finset.univ.erase (⟨3, by omega⟩ : Fin 4), D.W_F :=
              Finset.sum_le_sum fun r _ => hf0_deg (ir r) (hne_f0 r)
          _ = 3 * D.W_F := by simp
      rw [Finset.sum_add_distrib] at hS1 hS0
      have hsum_er0 : ∑ r : Fin 4, (D.f0.coeff (ir r)).natDegree =
          (D.f0.coeff (ir ⟨3, by omega⟩)).natDegree +
            ∑ r ∈ Finset.univ.erase (⟨3, by omega⟩ : Fin 4), (D.f0.coeff (ir r)).natDegree := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨3, by omega⟩ : Fin 4))]
      have hsum_jr : ∑ r' : Fin 5, (jr r' + 1) * wY = ((∑ r' : Fin 5, jr r') + 5) * wY := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp
      have hsum_ir_er : ∑ r ∈ Finset.univ.erase (⟨3, by omega⟩ : Fin 4), ir r * wY =
          ((∑ r : Fin 4, ir r) - 5) * wY := by
        rw [← Finset.sum_mul]
        have htot : ∑ r : Fin 4, ir r = 5 + ∑ r ∈ Finset.univ.erase (⟨3, by omega⟩ : Fin 4), ir r := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨3, by omega⟩ : Fin 4)), hir3]
        congr 1; omega
      have htot_w : ((∑ r' : Fin 5, jr r') + 5) * wY + ((∑ r : Fin 4, ir r) - 5) * wY = 20 * wY := by
        have h5le : 5 ≤ ∑ r : Fin 4, ir r := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨3, by omega⟩ : Fin 4)), hir3]; omega
        rw [← Nat.add_mul]; congr 1; omega
      omega

theorem natDegree_ResY_le : D.ResY.natDegree ≤ 9 * D.W_F - 25 * wY + 5 := by
  have h1 := D.natDegree_ResY_le_col1
  have h2 := D.natDegree_gj_le 2
  have h5 := D.hWF_lo
  omega

/-! ### Shifted `(A0_j, A1_j, B^{sh}_j)` at any point `(x0, y0)` -/

/-- Shifted `B^{sh}_j(T)` under `Y ↦ y0 + v` (`j = 0, 1, 2`). -/
noncomputable def Bsh (y0 : Fld) (j : Fin 3) : Fld[X] :=
  match j.val with
  | 0 => D.Bj 0 + C (y0 ^ 2) * D.Bj 1 + C (y0 ^ 4) * D.Bj 2
  | 1 => D.Bj 1
  | _ => D.Bj 2

/-- Shifted `A0_j(T)` under `Y ↦ y0 + v` (`j = 0, 1, 2`). -/
noncomputable def A0sh (y0 : Fld) (j : Fin 3) : Fld[X] :=
  match j.val with
  | 0 => D.Pj 0 + C (y0 ^ 2) * D.Pj 1 + C (y0 ^ 4) * D.Pj 2 + C y0 * D.Bsh y0 0
  | 1 => D.Pj 1 + C y0 * D.Bsh y0 1
  | _ => D.Pj 2 + C y0 * D.Bsh y0 2

/-- Shifted `A1_j(T)` under `X ↦ x0 + s, Y ↦ y0 + v` (`j = 0, 1, 2`). -/
noncomputable def A1sh (x0 y0 : Fld) (j : Fin 3) : Fld[X] :=
  match j.val with
  | 0 => D.Cj 0 + C (y0 ^ 2) * D.Cj 1 + C (y0 ^ 4) * D.Cj 2 + C x0 * D.Bsh y0 0
  | 1 => D.Cj 1 + C x0 * D.Bsh y0 1
  | _ => D.Cj 2 + C x0 * D.Bsh y0 2

lemma shiftBi_f0_eq (x0 y0 : Fld) :
    shiftBi x0 y0 D.f0 =
      ∑ j : Fin 3, (C (((D.A0sh y0 j).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) * X ^ (2 * j.val) +
        C (((D.Bsh y0 j).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) * X ^ (2 * j.val + 1)) := by
  have h2F : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
  have h2B : (2 : BiPoly Fld) = 0 := CharTwo.two_eq_zero
  have hsqX : (C x0 + X : Fld[X]) ^ 2 = C (x0 ^ 2) + X ^ 2 := by
    calc (C x0 + X : Fld[X]) ^ 2 = C x0 ^ 2 + 2 * C x0 * X + X ^ 2 := by ring
      _ = C (x0 ^ 2) + X ^ 2 := by rw [h2F, map_pow]; ring
  have hcompX : ∀ q : Fld[X], (q.comp (X ^ 2)).comp (C x0 + X) = (q.comp (C (x0 ^ 2) + X)).comp (X ^ 2) := fun q => by
    rw [comp_assoc, comp_assoc, pow_comp, X_comp, hsqX, add_comp, C_comp, X_comp]
  have hsqY : (C (C y0) + X : BiPoly Fld) ^ 2 = C (C (y0 ^ 2)) + X ^ 2 := by
    calc (C (C y0) + X : BiPoly Fld) ^ 2 = C (C y0) ^ 2 + 2 * C (C y0) * X + X ^ 2 := by ring
      _ = C (C (y0 ^ 2)) + X ^ 2 := by rw [h2B, map_pow, map_pow]; ring
  have hpow4Y : (C (C y0) + X : BiPoly Fld) ^ 4 = C (C (y0 ^ 4)) + X ^ 4 := by
    calc (C (C y0) + X : BiPoly Fld) ^ 4 = ((C (C y0) + X) ^ 2) ^ 2 := by ring
      _ = (C (C (y0 ^ 2)) + X ^ 2) ^ 2 := by rw [hsqY]
      _ = C (C (y0 ^ 2)) ^ 2 + 2 * C (C (y0 ^ 2)) * X ^ 2 + (X ^ 2) ^ 2 := by ring
      _ = C (C (y0 ^ 4)) + X ^ 4 := by rw [h2B, ← map_pow, ← map_pow]; ring_nf
  rw [D.f0_eq_sum, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, pow_zero, mul_one, zero_add, pow_one,
    shiftBi_add, shiftBi_mul, shiftBi_C, shiftBi_pow, shiftBi_X, hcompX]
  simp only [A0sh, Bsh, Fin.val_zero, Fin.val_one, Fin.val_two, add_comp, mul_comp, C_comp, map_add, map_mul]
  rw [show (C (C y0) + X : BiPoly Fld) ^ 3 = (C (C y0) + X) * (C (C y0) + X) ^ 2 by ring,
      show (C (C y0) + X : BiPoly Fld) ^ 5 = (C (C y0) + X) * (C (C y0) + X) ^ 4 by ring,
      hsqY, hpow4Y]
  generalize C (((D.Pj 0).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) = p0
  generalize C (((D.Pj 1).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) = p1
  generalize C (((D.Pj 2).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) = p2
  generalize C (((D.Bj 0).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) = b0
  generalize C (((D.Bj 1).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) = b1
  generalize C (((D.Bj 2).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) = b2
  ring

lemma shiftBi_f1_eq (x0 y0 : Fld) :
    shiftBi x0 y0 D.f1 =
      ∑ j : Fin 3, C (((D.A1sh x0 y0 j).comp (C (x0 ^ 2) + X)).comp (X ^ 2) +
        X * ((D.Bsh y0 j).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) * X ^ (2 * j.val) := by
  have h2F : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
  have h2B : (2 : BiPoly Fld) = 0 := CharTwo.two_eq_zero
  have hsqX : (C x0 + X : Fld[X]) ^ 2 = C (x0 ^ 2) + X ^ 2 := by
    calc (C x0 + X : Fld[X]) ^ 2 = C x0 ^ 2 + 2 * C x0 * X + X ^ 2 := by ring
      _ = C (x0 ^ 2) + X ^ 2 := by rw [h2F, map_pow]; ring
  have hcompX : ∀ q : Fld[X], (q.comp (X ^ 2)).comp (C x0 + X) = (q.comp (C (x0 ^ 2) + X)).comp (X ^ 2) := fun q => by
    rw [comp_assoc, comp_assoc, pow_comp, X_comp, hsqX, add_comp, C_comp, X_comp]
  have hsqY : (C (C y0) + X : BiPoly Fld) ^ 2 = C (C (y0 ^ 2)) + X ^ 2 := by
    calc (C (C y0) + X : BiPoly Fld) ^ 2 = C (C y0) ^ 2 + 2 * C (C y0) * X + X ^ 2 := by ring
      _ = C (C (y0 ^ 2)) + X ^ 2 := by rw [h2B, map_pow, map_pow]; ring
  have hpow4Y : (C (C y0) + X : BiPoly Fld) ^ 4 = C (C (y0 ^ 4)) + X ^ 4 := by
    calc (C (C y0) + X : BiPoly Fld) ^ 4 = ((C (C y0) + X) ^ 2) ^ 2 := by ring
      _ = (C (C (y0 ^ 2)) + X ^ 2) ^ 2 := by rw [hsqY]
      _ = C (C (y0 ^ 2)) ^ 2 + 2 * C (C (y0 ^ 2)) * X ^ 2 + (X ^ 2) ^ 2 := by ring
      _ = C (C (y0 ^ 4)) + X ^ 4 := by rw [h2B, ← map_pow, ← map_pow]; ring_nf
  rw [D.f1_eq_sum, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [gj, Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, pow_zero, mul_one,
    shiftBi_add, shiftBi_mul, shiftBi_C, shiftBi_pow, shiftBi_X,
    add_comp, mul_comp, X_comp, hcompX, map_add, map_mul]
  simp only [A1sh, Bsh, Fin.val_zero, Fin.val_one, Fin.val_two, add_comp, mul_comp, C_comp, map_add, map_mul]
  rw [hsqY, hpow4Y]
  generalize C (((D.Cj 0).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) = c0
  generalize C (((D.Cj 1).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) = c1
  generalize C (((D.Cj 2).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) = c2
  generalize C (((D.Bj 0).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) = b0
  generalize C (((D.Bj 1).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) = b1
  generalize C (((D.Bj 2).comp (C (x0 ^ 2) + X)).comp (X ^ 2)) = b2
  ring

/-- Exact local `T`-divisibility of `A0_j, A1_j, B^{sh}_j` at every domain point `i : Idx`! -/
theorem local_shifted_ords (i : Idx) (j : Fin 3) :
    let t0 : Fld := BinaryIRSProfile.domain i ^ 2
    (X - C t0) ^ (D.k i - j.val) ∣ D.A0sh (D.y i) j ∧
    (X - C t0) ^ (D.k i - j.val) ∣ D.A1sh (BinaryIRSProfile.domain i) (D.y i) j ∧
    (X - C t0) ^ (D.k i - 1 - j.val) ∣ D.Bsh (D.y i) j := by
  intro t0
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  have ⟨hm0, hm1⟩ := D.local_biMult_f0_f1 i
  have hcoeff0_ev : ∀ a, ((shiftBi x0 y0 D.f0).coeff (2 * j.val)).coeff (2 * a) =
      ((D.A0sh y0 j).comp (C t0 + X)).coeff a := by
    intro a; rw [D.shiftBi_f0_eq x0 y0, finset_sum_coeff, Finset.sum_eq_single j]
    · rw [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, if_pos rfl, if_neg (by omega), add_zero]
      exact comp_X_sq_coeff_even _ a
    · intro m _ hne
      have h1 : 2 * j.val ≠ 2 * m.val := by intro h; apply hne; ext; omega
      have h2 : 2 * j.val ≠ 2 * m.val + 1 := by omega
      rw [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, if_neg h1, if_neg h2, add_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcoeff0_od : ∀ a, ((shiftBi x0 y0 D.f0).coeff (2 * j.val + 1)).coeff (2 * a) =
      ((D.Bsh y0 j).comp (C t0 + X)).coeff a := by
    intro a; rw [D.shiftBi_f0_eq x0 y0, finset_sum_coeff, Finset.sum_eq_single j]
    · rw [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, if_neg (by omega), if_pos rfl, zero_add]
      exact comp_X_sq_coeff_even _ a
    · intro m _ hne
      have h1 : 2 * j.val + 1 ≠ 2 * m.val := by omega
      have h2 : 2 * j.val + 1 ≠ 2 * m.val + 1 := by intro h; apply hne; ext; omega
      rw [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, if_neg h1, if_neg h2, add_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcoeff1_ev : ∀ a, ((shiftBi x0 y0 D.f1).coeff (2 * j.val)).coeff (2 * a) =
      ((D.A1sh x0 y0 j).comp (C t0 + X)).coeff a := by
    intro a; rw [D.shiftBi_f1_eq x0 y0, finset_sum_coeff, Finset.sum_eq_single j]
    · rw [coeff_C_mul_X_pow, if_pos rfl, coeff_even_odd_pair]
      have hm : (2 * a) % 2 = 0 := by omega
      have hd : (2 * a) / 2 = a := by omega
      simp only [hm, hd, ↓reduceIte]
      rfl
    · intro m _ hne
      have h1 : 2 * j.val ≠ 2 * m.val := by intro h; apply hne; ext; omega
      rw [coeff_C_mul_X_pow, if_neg h1]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨pow_dvd_of_shift_coeff_zero _ t0 _ fun a ha => ?_,
          pow_dvd_of_shift_coeff_zero _ t0 _ fun a ha => ?_,
          pow_dvd_of_shift_coeff_zero _ t0 _ fun a ha => ?_⟩
  · rw [← hcoeff0_ev a]; exact hm0 (2 * a) (2 * j.val) (by omega)
  · rw [← hcoeff1_ev a]; exact hm1 (2 * a) (2 * j.val) (by omega)
  · rw [← hcoeff0_od a]; exact hm0 (2 * a) (2 * j.val + 1) (by omega)

lemma pow_dvd_g2_of_k (i : Idx) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i - 5) ∣ D.gj 2 := by
  have ⟨_, hA1, hB⟩ := D.local_shifted_ords i 2
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  have hg : D.gj 2 = (D.A1sh x0 y0 2).comp (X ^ 2) + (X - C x0) * (D.Bsh y0 2).comp (X ^ 2) := by
    simp only [gj, A1sh, Bsh, Fin.val_two, add_comp, mul_comp, C_comp, sub_eq_add_neg, CharTwo.neg_eq]
    have hx : C x0 * (D.Bj 2).comp (X ^ 2) + C x0 * (D.Bj 2).comp (X ^ 2) = 0 := CharTwo.add_self_eq_zero _
    linear_combination -hx
  rw [hg]
  apply dvd_add
  · refine (pow_dvd_pow (X - C x0) (show 2 * D.k i - 5 ≤ 2 * (D.k i - 2) by omega)).trans ?_
    exact (pow_dvd_comp_X_sq_iff _ x0 _).mpr hA1
  · by_cases hk3 : 3 ≤ D.k i
    · have hexp : 2 * D.k i - 5 = 1 + 2 * (D.k i - 1 - 2) := by omega
      rw [hexp, pow_add, pow_one]
      exact mul_dvd_mul dvd_rfl ((pow_dvd_comp_X_sq_iff _ x0 _).mpr hB)
    · have : 2 * D.k i - 5 = 0 := by omega
      rw [this, pow_zero]; exact one_dvd _

lemma pow_dvd_f1_eval_P (i : Idx) (hi : i ∈ D.Az) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i - 1) ∣ D.f1.eval D.P := by
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  have hP0 : D.P.eval x0 = y0 := D.hagree i hi
  have ⟨_, hm1⟩ := D.local_biMult_f0_f1 i
  apply pow_dvd_of_shift_coeff_zero _ x0 _
  have hsh : (D.f1.eval D.P).comp (C x0 + X) =
      (shiftBi x0 y0 D.f1).eval (D.P.comp (C x0 + X) - C y0) := by
    unfold shiftBi
    rw [Polynomial.eval_comp, eval_add, eval_C, eval_X, add_sub_cancel]
    exact (Polynomial.eval_map_apply (f := Polynomial.compRingHom (C x0 + X)) (x := D.P) (p := D.f1)).symm
  rw [hsh]
  have hPsh_dvd : X ∣ (D.P.comp (C x0 + X) - C y0) := by
    rw [X_dvd_iff, coeff_sub, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_C, eval_X, add_zero,
      coeff_C_zero, hP0, sub_self]
  set Q := D.P.comp (C x0 + X) - C y0
  have hdvd_tot : X ^ (2 * D.k i - 1) ∣ (shiftBi x0 y0 D.f1).eval Q := by
    rw [eval_eq_sum_range]
    apply Finset.dvd_sum; intro j _
    have hcj : X ^ (2 * D.k i - 1 - j) ∣ (shiftBi x0 y0 D.f1).coeff j := by
      simpa only [one_mul] using (biMultGE_iff_weightedOrdGE_one x0 y0 D.f1 (2 * D.k i - 1)).mp hm1 j
    have hQj : X ^ j ∣ Q ^ j := pow_dvd_pow_of_dvd hPsh_dvd j
    exact (pow_dvd_pow X (show 2 * D.k i - 1 ≤ (2 * D.k i - 1 - j) + j by omega)).trans
      (by rw [pow_add]; exact mul_dvd_mul hcj hQj)
  exact X_pow_dvd_iff.mp hdvd_tot

/-- Exact resultant local order lower bound at `U = 0` (`0, 1, 11, 29 + 18(k-3)`). -/
def resOrdU0 (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 11 else 29 + 18 * (k - 3)

/-- Exact resultant local order lower bound at `U ≠ 0` (`0, 4, 16, 34 + 18(k-3)`). -/
def resOrdU1 (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 4 else if k = 2 then 16 else 34 + 18 * (k - 3)

/-- Universal local order theorem for `Res_Y^{(5, 4)}` at ANY point `i : Idx`, parameterized
by `uBonus ∈ {0, 1}` (`uBonus = 1` when `(X - C t0)^(k - j) ∣ B^{sh}_j`)! -/
theorem pow_dvd_ResY_general (i : Idx) (uBonus : ℕ) (hu : uBonus ≤ 1)
    (hB_ext : ∀ j : Fin 3, (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (D.k i - (1 - uBonus) - j.val) ∣ D.Bsh (D.y i) j) :
    (X - C (BinaryIRSProfile.domain i)) ^ (if uBonus = 0 then resOrdU0 (D.k i) else resOrdU1 (D.k i)) ∣ D.ResY := by
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  set t0 := x0 ^ 2
  set k := D.k i
  by_cases hk0 : k = 0
  · simp [hk0, resOrdU0, resOrdU1]
  -- Translate to s = 0 via resultant_shiftBi!
  have hshift_res : Polynomial.resultant (shiftBi x0 y0 D.f0) (shiftBi x0 y0 D.f1) 5 4 =
      D.ResY.comp (C x0 + X) :=
    resultant_shiftBi x0 y0 D.f0 D.f1 5 4 D.f0_natDegree_le (le_of_eq D.f1_natDegree_eq)
  suffices hX : X ^ (if uBonus = 0 then resOrdU0 k else resOrdU1 k) ∣
      Polynomial.resultant (shiftBi x0 y0 D.f0) (shiftBi x0 y0 D.f1) 5 4 by
    rw [hshift_res] at hX
    exact pow_dvd_of_shift_coeff_zero D.ResY x0 _ (X_pow_dvd_iff.mp hX)
  by_cases hk1 : k = 1
  · -- k = 1: use pow_dvd_resultant_of_biMultGE directly (gives 1 for uBonus=0, 4 for uBonus=1)!
    have h1 : resOrdExact 5 (1 + uBonus) 4 (1 + uBonus) = if uBonus = 0 then 1 else 4 := by
      rcases (show uBonus = 0 ∨ uBonus = 1 by omega) with rfl | rfl <;> decide
    have hm0 : biMultGE x0 y0 D.f0 (1 + uBonus) := by
      intro a b hab
      rw [D.shiftBi_f0_eq x0 y0, finset_sum_coeff, finset_sum_coeff]
      apply Finset.sum_eq_zero; intro j _
      rw [coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
      have hA : (if b = 2 * j.val then ((D.A0sh y0 j).comp (C t0 + X)).comp (X ^ 2) else 0).coeff a = 0 := by
        split_ifs with hb
        · by_cases ha : a % 2 = 0
          · rw [show a = 2 * (a / 2) by omega, comp_X_sq_coeff_even]
            exact shift_coeff_zero_of_pow_dvd _ t0 _ (D.local_shifted_ords i j).1 (a / 2) (by omega)
          · rw [show a = 2 * (a / 2) + 1 by omega, comp_X_sq_coeff_odd]
        · simp
      have hB : (if b = 2 * j.val + 1 then ((D.Bsh y0 j).comp (C t0 + X)).comp (X ^ 2) else 0).coeff a = 0 := by
        split_ifs with hb
        · by_cases ha : a % 2 = 0
          · rw [show a = 2 * (a / 2) by omega, comp_X_sq_coeff_even]
            exact shift_coeff_zero_of_pow_dvd _ t0 _ (hB_ext j) (a / 2) (by omega)
          · rw [show a = 2 * (a / 2) + 1 by omega, comp_X_sq_coeff_odd]
        · simp
      rw [hA, hB, add_zero]
    have hm1 : biMultGE x0 y0 D.f1 (1 + uBonus) := by
      intro a b hab
      rw [D.shiftBi_f1_eq x0 y0, finset_sum_coeff, finset_sum_coeff]
      apply Finset.sum_eq_zero; intro j _
      rw [coeff_C_mul_X_pow]
      split_ifs with hb
      · rw [coeff_even_odd_pair]
        split_ifs with ha
        · exact shift_coeff_zero_of_pow_dvd _ t0 _ (D.local_shifted_ords i j).2.1 (a / 2) (by omega)
        · exact shift_coeff_zero_of_pow_dvd _ t0 _ (hB_ext j) (a / 2) (by omega)
      · simp
    have hd := pow_dvd_resultant_of_biMultGE x0 y0 D.f0 D.f1 5 (1 + uBonus) 4 (1 + uBonus)
      hm0 hm1 D.f0_natDegree_le (le_of_eq D.f1_natDegree_eq)
    rw [h1] at hd
    simpa [hk1, resOrdU0, resOrdU1] using hd
  · -- k ≥ 2: use char2_resultant_5_4_eq_5_2 + pow_dvd_resultant_of_weighted_ord (w = 2)!
    have hk2 : 2 ≤ k := by omega
    let Esh : BiPoly Fld :=
      ∑ j : Fin 3, C (((D.A0sh y0 j).comp (C t0 + X)).comp (X ^ 2)) * X ^ j.val
    let Osh : BiPoly Fld :=
      ∑ j : Fin 3, C (((D.Bsh y0 j).comp (C t0 + X)).comp (X ^ 2)) * X ^ j.val
    let A1s : BiPoly Fld :=
      ∑ j : Fin 3, C (((D.A1sh x0 y0 j).comp (C t0 + X)).comp (X ^ 2)) * X ^ j.val
    let Gsh : BiPoly Fld := A1s + C X * Osh
    have hf0_sh : shiftBi x0 y0 D.f0 = Esh.comp (X ^ 2) + X * Osh.comp (X ^ 2) := by
      rw [D.shiftBi_f0_eq x0 y0]
      simp only [Esh, Osh, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
        add_comp, mul_comp, C_comp, pow_comp, X_comp, pow_zero, pow_one, mul_zero, mul_one, zero_add]
      ring
    have hf1_sh : shiftBi x0 y0 D.f1 = Gsh.comp (X ^ 2) := by
      rw [D.shiftBi_f1_eq x0 y0]
      simp only [Gsh, A1s, Osh, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
        add_comp, mul_comp, C_comp, pow_comp, X_comp, pow_zero, pow_one, mul_zero, mul_one, map_add, map_mul]
      ring
    have hEdeg : Esh.natDegree ≤ 2 := by
      refine (natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
      exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _ |>.trans (by have := j.isLt; omega))
    have hOdeg : Osh.natDegree ≤ 2 := by
      refine (natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
      exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _ |>.trans (by have := j.isLt; omega))
    have hA1deg : A1s.natDegree ≤ 2 := by
      refine (natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
      exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _ |>.trans (by have := j.isLt; omega))
    have hGdeg : Gsh.natDegree ≤ 2 :=
      (natDegree_add_le _ _).trans (max_le hA1deg ((natDegree_C_mul_le _ _).trans hOdeg))
    let Ψ : BiPoly Fld := C (X ^ 2) * Esh ^ 2 + X * A1s ^ 2
    have hG_add : Gsh + C X * Osh = A1s := by
      dsimp only [Gsh]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    -- Lift to RatFunc Fld via polymorphic helper!
    have hres_eq : X ^ 4 * Polynomial.resultant (shiftBi x0 y0 D.f0) (shiftBi x0 y0 D.f1) 5 4 =
        Polynomial.resultant Ψ Gsh 5 2 := by
      have hg2_sh_ne : Gsh.coeff 2 ≠ 0 := by
        have h2 : Gsh.coeff 2 = (D.gj 2).comp (C x0 + X) := by
          have h := congrArg (fun p : BiPoly Fld => p.coeff 4) hf1_sh
          have hL : (shiftBi x0 y0 D.f1).coeff 4 = (D.gj 2).comp (C x0 + X) := by
            rw [D.shiftBi_f1_eq x0 y0, finset_sum_coeff, Finset.sum_eq_single (2 : Fin 3)]
            · simp only [coeff_C_mul_X_pow, Fin.val_two, ↓reduceIte]
              have h2F : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
              have hsqX : (C x0 + X : Fld[X]) ^ 2 = C (x0 ^ 2) + X ^ 2 := by
                calc (C x0 + X : Fld[X]) ^ 2 = C x0 ^ 2 + 2 * C x0 * X + X ^ 2 := by ring
                  _ = C (x0 ^ 2) + X ^ 2 := by rw [h2F, map_pow]; ring
              have hcompX : ∀ q : Fld[X], (q.comp (X ^ 2)).comp (C x0 + X) = (q.comp (C (x0 ^ 2) + X)).comp (X ^ 2) := fun q => by
                rw [comp_assoc, comp_assoc, pow_comp, X_comp, hsqX, add_comp, C_comp, X_comp]
              simp only [gj, A1sh, Bsh, Fin.val_two, add_comp, mul_comp, C_comp, X_comp, hcompX, t0]
              ring
            · intro j _ hne; have : 4 ≠ 2 * j.val := by have := j.isLt; intro he; apply hne; ext; omega
              rw [coeff_C_mul_X_pow, if_neg this]
            · intro h; exact absurd (Finset.mem_univ _) h
          rw [hL] at h
          have hR : (Gsh.comp (X ^ 2)).coeff 4 = Gsh.coeff 2 := comp_X_sq_coeff_even Gsh 2
          rw [hR] at h; exact h.symm
        rw [h2]; intro h0; apply D.g2_ne_zero
        have hb := congrArg (fun p : Fld[X] => p.comp (X - C x0)) h0
        simp only [comp_assoc, add_comp, X_comp, C_comp, add_sub_cancel, comp_X, zero_comp] at hb
        exact hb
      haveI : CharP (RatFunc Fld) 2 :=
        charP_of_injective_algebraMap (IsFractionRing.injective Fld[X] (RatFunc Fld)) 2
      rw [hf0_sh, hf1_sh]
      exact res_5_4_eq_5_2_of_inj (algebraMap Fld[X] (RatFunc Fld))
        (IsFractionRing.injective Fld[X] (RatFunc Fld)) Esh Osh A1s Gsh Ψ hEdeg hOdeg hGdeg hg2_sh_ne hG_add rfl
    -- Prove weighted order (w = 2) of Ψ ≥ 4*k + 2 and Gsh ≥ 2*k - 1 + uBonus!
    have hΨ_ord : ∀ r, X ^ (4 * k + 2 - 2 * r) ∣ Ψ.coeff r := by
      intro r
      have h2B : (2 : BiPoly Fld) = 0 := CharTwo.two_eq_zero
      have hsq_sum : ∀ (p : BiPoly Fld), p.natDegree ≤ 2 →
          p ^ 2 = ∑ j : Fin 3, C ((p.coeff j.val) ^ 2) * X ^ (2 * j.val) := by
        intro p hp
        have hexp : p = C (p.coeff 0) + C (p.coeff 1) * X + C (p.coeff 2) * X ^ 2 := by
          ext m; cases m with
          | zero => simp [coeff_C, coeff_X, coeff_X_pow]
          | succ m' => cases m' with
            | zero => simp [coeff_C, coeff_X, coeff_X_pow]
            | succ m'' => cases m'' with
              | zero => simp [coeff_C, coeff_X, coeff_X_pow]
              | succ m''' =>
                  rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega))]
                  simp [coeff_C, coeff_X, coeff_X_pow]
        rw [Fin.sum_univ_three]
        conv_lhs => rw [hexp]
        simp only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, pow_zero, mul_one, map_pow]
        calc (C (p.coeff 0) + C (p.coeff 1) * X + C (p.coeff 2) * X ^ 2) ^ 2
            = C (p.coeff 0) ^ 2 + C (p.coeff 1) ^ 2 * X ^ 2 + C (p.coeff 2) ^ 2 * X ^ 4 +
              2 * (C (p.coeff 0) * C (p.coeff 1) * X + C (p.coeff 0) * C (p.coeff 2) * X ^ 2 +
                   C (p.coeff 1) * C (p.coeff 2) * X ^ 3) := by ring
          _ = C (p.coeff 0) ^ 2 + C (p.coeff 1) ^ 2 * X ^ 2 + C (p.coeff 2) ^ 2 * X ^ 4 := by rw [h2B]; ring
      have hEcoeff : ∀ j : Fin 3, Esh.coeff j.val = ((D.A0sh y0 j).comp (C t0 + X)).comp (X ^ 2) := by
        intro j; dsimp only [Esh]; rw [finset_sum_coeff, Finset.sum_eq_single j]
        · simp [coeff_C_mul_X_pow]
        · intro m _ hne; rw [coeff_C_mul_X_pow, if_neg (fun h => hne (Fin.ext h.symm))]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hA1coeff : ∀ j : Fin 3, A1s.coeff j.val = ((D.A1sh x0 y0 j).comp (C t0 + X)).comp (X ^ 2) := by
        intro j; dsimp only [A1s]; rw [finset_sum_coeff, Finset.sum_eq_single j]
        · simp [coeff_C_mul_X_pow]
        · intro m _ hne; rw [coeff_C_mul_X_pow, if_neg (fun h => hne (Fin.ext h.symm))]
        · intro h; exact absurd (Finset.mem_univ _) h
      dsimp only [Ψ]
      rw [hsq_sum Esh hEdeg, hsq_sum A1s hA1deg, coeff_add, coeff_C_mul, finset_sum_coeff, Finset.mul_sum]
      apply dvd_add
      · apply Finset.dvd_sum; intro j _
        rw [coeff_C_mul_X_pow]
        split_ifs with hr
        · subst hr
          have hd := (D.local_shifted_ords i j).1
          have hx : X ^ (k - j.val) ∣ (D.A0sh y0 j).comp (C t0 + X) :=
            X_pow_dvd_iff.mpr (shift_coeff_zero_of_pow_dvd _ t0 _ hd)
          have hx2 : X ^ (2 * (k - j.val)) ∣ ((D.A0sh y0 j).comp (C t0 + X)).comp (X ^ 2) := by
            rcases hx with ⟨q, hq⟩; refine ⟨q.comp (X ^ 2), ?_⟩
            rw [hq, mul_comp, pow_comp, X_comp, ← pow_mul, mul_comm]
          have hx4 : X ^ (4 * (k - j.val)) ∣ (((D.A0sh y0 j).comp (C t0 + X)).comp (X ^ 2)) ^ 2 := by
            rw [show 4 * (k - j.val) = 2 * (k - j.val) * 2 by ring, pow_mul]
            exact pow_dvd_pow_of_dvd hx2 2
          rw [hEcoeff j]
          exact (pow_dvd_pow X (show 4 * k + 2 - 2 * (2 * j.val) ≤ 2 + 4 * (k - j.val) by omega)).trans
            (by rw [pow_add]; exact mul_dvd_mul dvd_rfl hx4)
        · rw [mul_zero]; exact dvd_zero _
      · cases r with
        | zero => simp
        | succ r' =>
            rw [coeff_X_mul, finset_sum_coeff]
            apply Finset.dvd_sum; intro j _
            rw [coeff_C_mul_X_pow]
            split_ifs with hr
            · subst hr
              have hd := (D.local_shifted_ords i j).2.1
              have hx : X ^ (k - j.val) ∣ (D.A1sh x0 y0 j).comp (C t0 + X) :=
                X_pow_dvd_iff.mpr (shift_coeff_zero_of_pow_dvd _ t0 _ hd)
              have hx2 : X ^ (2 * (k - j.val)) ∣ ((D.A1sh x0 y0 j).comp (C t0 + X)).comp (X ^ 2) := by
                rcases hx with ⟨q, hq⟩; refine ⟨q.comp (X ^ 2), ?_⟩
                rw [hq, mul_comp, pow_comp, X_comp, ← pow_mul, mul_comm]
              have hx4 : X ^ (4 * (k - j.val)) ∣ (((D.A1sh x0 y0 j).comp (C t0 + X)).comp (X ^ 2)) ^ 2 := by
                rw [show 4 * (k - j.val) = 2 * (k - j.val) * 2 by ring, pow_mul]
                exact pow_dvd_pow_of_dvd hx2 2
              rw [hA1coeff j]
              exact (pow_dvd_pow X (show 4 * k + 2 - 2 * (2 * j.val + 1) ≤ 4 * (k - j.val) by omega)).trans hx4
            · exact dvd_zero _
    have hG_ord : ∀ r, X ^ (2 * k - 1 + uBonus - 2 * r) ∣ Gsh.coeff r := by
      intro r
      by_cases hr3 : r < 3
      · let j : Fin 3 := ⟨r, hr3⟩
        have hGj : Gsh.coeff r = ((D.A1sh x0 y0 j).comp (C t0 + X)).comp (X ^ 2) +
            X * ((D.Bsh y0 j).comp (C t0 + X)).comp (X ^ 2) := by
          dsimp only [Gsh, A1s, Osh]; rw [coeff_add, coeff_C_mul, finset_sum_coeff, finset_sum_coeff,
            Finset.sum_eq_single j, Finset.sum_eq_single j]
          · simp [coeff_C_mul_X_pow, j]
          · intro m _ hne; rw [coeff_C_mul_X_pow, if_neg (fun h => hne (Fin.ext h.symm))]
          · intro h; exact absurd (Finset.mem_univ _) h
          · intro m _ hne; rw [coeff_C_mul_X_pow, if_neg (fun h => hne (Fin.ext h.symm))]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hGj]
        apply dvd_add
        · have hx : X ^ (k - r) ∣ (D.A1sh x0 y0 j).comp (C t0 + X) :=
            X_pow_dvd_iff.mpr (shift_coeff_zero_of_pow_dvd _ t0 _ (D.local_shifted_ords i j).2.1)
          have hx2 : X ^ (2 * (k - r)) ∣ ((D.A1sh x0 y0 j).comp (C t0 + X)).comp (X ^ 2) := by
            rcases hx with ⟨q, hq⟩; refine ⟨q.comp (X ^ 2), ?_⟩
            rw [hq, mul_comp, pow_comp, X_comp, ← pow_mul, mul_comm]
          exact (pow_dvd_pow X (show 2 * k - 1 + uBonus - 2 * r ≤ 2 * (k - r) by omega)).trans hx2
        · have hx : X ^ (k - (1 - uBonus) - r) ∣ (D.Bsh y0 j).comp (C t0 + X) :=
            X_pow_dvd_iff.mpr (shift_coeff_zero_of_pow_dvd _ t0 _ (hB_ext j))
          have hx2 : X ^ (2 * (k - (1 - uBonus) - r)) ∣ ((D.Bsh y0 j).comp (C t0 + X)).comp (X ^ 2) := by
            rcases hx with ⟨q, hq⟩; refine ⟨q.comp (X ^ 2), ?_⟩
            rw [hq, mul_comp, pow_comp, X_comp, ← pow_mul, mul_comm]
          exact (pow_dvd_pow X (show 2 * k - 1 + uBonus - 2 * r ≤ 1 + 2 * (k - (1 - uBonus) - r) by omega)).trans
            (by rw [pow_add, pow_one]; exact mul_dvd_mul dvd_rfl hx2)
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hGdeg (by omega))]; exact dvd_zero _
    have hΨdeg : Ψ.natDegree ≤ 5 := by
      refine (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by omega))) ?_)
      have hx1 : (X : BiPoly Fld).natDegree ≤ 1 := natDegree_X_le
      have hsq4 : (A1s ^ 2).natDegree ≤ 4 := natDegree_pow_le.trans (by omega)
      exact natDegree_mul_le.trans (by omega)
    have hdvd_w := pow_dvd_resultant_of_weighted_ord (X : Fld[X]) Ψ Gsh 5 (4 * k + 2) 2 (2 * k - 1 + uBonus) 2
      hΨdeg hGdeg hΨ_ord hG_ord
    rw [← hres_eq] at hdvd_w
    -- Every gain in allGainsSorted is ≤ 2, so take 10 has sum ≤ 20!
    have htake_le : ((allGainsSorted 5 (4 * k + 2) 2 (2 * k - 1 + uBonus) 2).take (5 * 2)).sum ≤ 20 := by
      have hall2 : ∀ x ∈ allGainsSorted 5 (4 * k + 2) 2 (2 * k - 1 + uBonus) 2, x ≤ 2 := by
        intro x hx
        unfold allGainsSorted at hx
        have hmem := (List.mergeSort_perm _ (fun a b : ℕ => decide (a ≥ b))).mem_iff.mp hx
        simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_replicate] at hmem
        rcases hmem with ⟨i', _, _, rfl⟩ | ⟨j', _, _, rfl⟩ <;> unfold stepGain <;> omega
      have hsub : ∀ (l : List ℕ) (n : ℕ), (∀ x ∈ l, x ≤ 2) → (l.take n).sum ≤ 2 * n := by
        intro l; induction l with
        | nil => intro n _; simp
        | cons a t ih =>
            intro n h
            cases n with
            | zero => simp
            | succ n' =>
                simp only [List.take_succ_cons, List.sum_cons]
                have ha := h a (by simp)
                have ht := ih n' (fun y hy => h y (by simp [hy]))
                omega
      exact hsub _ 10 hall2
    have hge : 4 + (if uBonus = 0 then resOrdU0 k else resOrdU1 k) ≤
        resOrdWeighted 5 (4 * k + 2) 2 (2 * k - 1 + uBonus) 2 := by
      unfold resOrdWeighted
      simp only [show (5 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega, ↓reduceIte]
      rcases (show uBonus = 0 ∨ uBonus = 1 by omega) with rfl | rfl <;>
        (simp only [resOrdU0, resOrdU1, hk0, hk1, ↓reduceIte]; split_ifs <;> omega)
    have hdvd2 := (pow_dvd_pow (X : Fld[X]) hge).trans hdvd_w
    rw [pow_add] at hdvd2
    exact (mul_dvd_mul_iff_left (pow_ne_zero 4 X_ne_zero)).mp hdvd2

theorem pow_dvd_ResY_U0 (i : Idx) :
    (X - C (BinaryIRSProfile.domain i)) ^ resOrdU0 (D.k i) ∣ D.ResY := by
  simpa using D.pow_dvd_ResY_general i 0 (by omega) fun j => (D.local_shifted_ords i j).2.2

/-! ### Part 5: Common Point Counts & `baseT4Rows` Satisfaction -/

def n0 (D : KerD45Data) : ℕ := (Finset.univ.filter fun i : Idx => D.k i = 0).card
def n1 (D : KerD45Data) : ℕ := (Finset.univ.filter fun i : Idx => D.k i = 1).card
def n2 (D : KerD45Data) : ℕ := (Finset.univ.filter fun i : Idx => D.k i = 2).card
def n3 (D : KerD45Data) : ℕ := (Finset.univ.filter fun i : Idx => 3 ≤ D.k i).card
def nt (D : KerD45Data) : ℕ := ∑ i : Idx, (D.k i - 3)
def a0 (D : KerD45Data) : ℕ := (D.Az.filter fun i : Idx => D.k i = 0).card
def a1 (D : KerD45Data) : ℕ := (D.Az.filter fun i : Idx => D.k i = 1).card
def a2 (D : KerD45Data) : ℕ := (D.Az.filter fun i : Idx => D.k i = 2).card
def a3 (D : KerD45Data) : ℕ := (D.Az.filter fun i : Idx => 3 ≤ D.k i).card

attribute [irreducible] n0 n1 n2 n3 nt a0 a1 a2 a3

lemma n_sum_eq_N : D.n0 + D.n1 + D.n2 + D.n3 = N := by
  have hgen : ∀ S : Finset Idx,
      (S.filter fun i => D.k i = 0).card + (S.filter fun i => D.k i = 1).card +
      (S.filter fun i => D.k i = 2).card + (S.filter fun i => 3 ≤ D.k i).card = S.card := by
    intro S
    have h1 : ∑ _i ∈ S, (1 : ℕ) =
        (∑ i ∈ S, if D.k i = 0 then 1 else 0) + (∑ i ∈ S, if D.k i = 1 then 1 else 0) +
        (∑ i ∈ S, if D.k i = 2 then 1 else 0) + (∑ i ∈ S, if 3 ≤ D.k i then 1 else 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; split_ifs <;> omega
    simp only [Finset.sum_const, smul_eq_mul, mul_one, ← Finset.card_filter] at h1
    exact h1.symm
  unfold n0 n1 n2 n3
  exact (hgen Finset.univ).trans BinaryIRSProfile.card_index

lemma a_sum_eq_card : D.a0 + D.a1 + D.a2 + D.a3 = D.Az.card := by
  have h1 : ∑ i ∈ D.Az, (1 : ℕ) =
      (∑ i ∈ D.Az, if D.k i = 0 then 1 else 0) + (∑ i ∈ D.Az, if D.k i = 1 then 1 else 0) +
      (∑ i ∈ D.Az, if D.k i = 2 then 1 else 0) + (∑ i ∈ D.Az, if 3 ≤ D.k i then 1 else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> omega
  simp only [Finset.sum_const, smul_eq_mul, mul_one, ← Finset.card_filter] at h1
  unfold a0 a1 a2 a3; exact h1.symm

lemma a_le_n : D.a0 ≤ D.n0 ∧ D.a1 ≤ D.n1 ∧ D.a2 ≤ D.n2 ∧ D.a3 ≤ D.n3 := by
  unfold a0 a1 a2 a3 n0 n1 n2 n3
  refine ⟨Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _)),
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _)),
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _)),
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))⟩

lemma a1_3a2_5a3_le : D.a1 + 3 * D.a2 + 5 * D.a3 ≤ D.W_F - wY + 1 := by
  have hsum : D.a1 + 3 * D.a2 + 5 * D.a3 ≤ ∑ i ∈ D.Az, (2 * D.k i - 1) := by
    have hrew : D.a1 + 3 * D.a2 + 5 * D.a3 =
        ∑ i ∈ D.Az, ((if D.k i = 1 then 1 else 0) + (if D.k i = 2 then 3 else 0) + (if 3 ≤ D.k i then 5 else 0)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
      unfold a1 a2 a3; ring
    rw [hrew]; apply Finset.sum_le_sum; intro i _; split_ifs <;> omega
  exact hsum.trans ((sum_ord_le_natDegree_of_dvd D.Az BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    (D.f1.eval D.P) D.f1_eval_P_ne_zero _ D.pow_dvd_f1_eval_P).trans D.natDegree_f1_eval_P_le)

lemma n3_2nt_le : D.n3 + 2 * D.nt ≤ D.W_F + 1 - 5 * wY := by
  have hsum : D.n3 + 2 * D.nt = ∑ i : Idx, (2 * D.k i - 5) := by
    have hgen : ∀ S : Finset Idx,
        (S.filter fun i => 3 ≤ D.k i).card + 2 * ∑ i ∈ S, (D.k i - 3) = ∑ i ∈ S, (2 * D.k i - 5) := by
      intro S
      have hrew : (S.filter fun i => 3 ≤ D.k i).card + 2 * ∑ i ∈ S, (D.k i - 3) =
          ∑ i ∈ S, ((if 3 ≤ D.k i then 1 else 0) + 2 * (D.k i - 3)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
      rw [hrew]; apply Finset.sum_congr rfl; intro i _; split_ifs <;> omega
    unfold n3 nt; exact hgen Finset.univ
  rw [hsum]
  exact (sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    (D.gj 2) D.g2_ne_zero _ (fun i _ => D.pow_dvd_g2_of_k i)).trans (D.natDegree_gj_le 2)

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
  let x : Fin 10 → ℚ := fun j =>
    match j.val with
    | 0 => (D.n0 : ℚ) / (N : ℚ) | 1 => (D.n1 : ℚ) / (N : ℚ)
    | 2 => (D.n2 : ℚ) / (N : ℚ) | 3 => (D.n3 : ℚ) / (N : ℚ)
    | 4 => (D.nt : ℚ) / (N : ℚ) | 5 => (D.a0 : ℚ) / (N : ℚ)
    | 6 => (D.a1 : ℚ) / (N : ℚ) | 7 => (D.a2 : ℚ) / (N : ℚ)
    | 8 => (D.a3 : ℚ) / (N : ℚ) | _ => (D.W_F : ℚ) / (wY : ℚ)
  refine ⟨x, fun j => by dsimp only [x]; split <;> positivity, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only [t4aNumVars]
  have hBV := baseT4Rows_valid (nv := 10) (ic := 9) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD
  have hBS := D.baseT4Rows_sat (nv := 10) (ic := 9) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD x
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcLo hcHi hloG hhiG
  have hc_nn : (0 : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ) := by positivity
  have hN_eq : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  have hResB : D.n1 + 11 * D.n2 + 29 * D.n3 + 18 * D.nt ≤ 9 * D.W_F - 25 * wY + 5 :=
    D.resOrdU0_le_natDegree.trans D.natDegree_ResY_le
  have hDetB : 2 * (2 * D.n2 + 5 * D.n3 + 3 * D.nt) ≤ 3 * D.W_F - 8 * wY + 1 := by
    have hsum : 2 * D.n2 + 5 * D.n3 + 3 * D.nt = ∑ i : Idx, detOrd (D.k i) := by
      have hgen : ∀ S : Finset Idx,
          2 * (S.filter fun i => D.k i = 2).card + 5 * (S.filter fun i => 3 ≤ D.k i).card +
          3 * ∑ i ∈ S, (D.k i - 3) = ∑ i ∈ S, detOrd (D.k i) := by
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
    omega
  constructor
  · intro r hr
    simp only [buildT4ARows, t4aNumVars, t4aStaticRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact ⟨hBV.1 r hr, hBS.1 r hr⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (1 : ℕ) < 10 by omega, show (2 : ℕ) < 10 by omega, show (3 : ℕ) < 10 by omega,
          show (4 : ℕ) < 10 by omega, show (9 : ℕ) < 10 by omega, ↓reduceDIte, ↓reduceIte, x, cI_mul_div_N, cH_mul_c_eq]
        have hResQ : (D.n1 : ℚ) + 11 * (D.n2 : ℚ) + 29 * (D.n3 : ℚ) + 18 * (D.nt : ℚ) ≤
            9 * (D.W_F : ℚ) - 25 * (wY : ℚ) + 5 := by
          have h25 : 25 * wY ≤ 9 * D.W_F := by have := D.hWF_lo; have := D.hwY_pos; omega
          have hZ : ((D.n1 + 11 * D.n2 + 29 * D.n3 + 18 * D.nt : ℕ) : ℤ) ≤ 9 * (D.W_F : ℤ) - 25 * (wY : ℤ) + 5 := by omega
          exact_mod_cast hZ
        push_cast; rw [hN_eq]; linarith
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (2 : ℕ) < 10 by omega, show (3 : ℕ) < 10 by omega, show (4 : ℕ) < 10 by omega,
          show (9 : ℕ) < 10 by omega, ↓reduceDIte, ↓reduceIte, x, cI_mul_div_N, cQ_mul_c_eq]
        have hDetQ : 2 * (2 * (D.n2 : ℚ) + 5 * (D.n3 : ℚ) + 3 * (D.nt : ℚ)) ≤
            3 * (D.W_F : ℚ) - 8 * (wY : ℚ) + 1 := by
          have h8 : 8 * wY ≤ 3 * D.W_F := by have := D.hWF_lo; have := D.hwY_pos; omega
          have hZ : ((2 * (2 * D.n2 + 5 * D.n3 + 3 * D.nt) : ℕ) : ℤ) ≤ 3 * (D.W_F : ℤ) - 8 * (wY : ℤ) + 1 := by omega
          exact_mod_cast hZ
        push_cast; rw [hN_eq]; linarith
  · intro r hr
    simp only [buildT4ARows, t4aNumVars, t4aStaticRows, List.toList_toArray, List.append_nil] at hr
    exact ⟨hBV.2 r hr, hBS.2 r hr⟩

/-- Primitive coprime syzygy extraction whenever `detM = 0`. -/
lemma exists_coprime_syzygy (hdet0 : D.detM = 0) :
    ∃ p c b : Fld[X],
      (p ≠ 0 ∨ c ≠ 0 ∨ b ≠ 0) ∧
      (∀ d : Fld[X], d ∣ p → d ∣ c → d ∣ b → IsUnit d) ∧
      (∀ j : Fin 3, p * D.Pj j + c * D.Cj j + b * D.Bj j = 0) := by
  obtain ⟨p0, c0, b0, hne0, hsyzM⟩ := exists_poly_syzygy_of_det_zero
    (algebraMap Fld[X] (RatFunc Fld)) (IsFractionRing.injective Fld[X] (RatFunc Fld))
    (fun x => by
      obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors Fld[X]) x
      exact ⟨n, d, nonZeroDivisors.ne_zero d.2, hd⟩)
    D.coeffMat hdet0
  have hsyz0 : ∀ j : Fin 3, p0 * D.Pj j + c0 * D.Cj j + b0 * D.Bj j = 0 := fun j => by
    simpa [coeffMat] using hsyzM j
  obtain ⟨g, p, c, b, hg_ne, hp, hc, hb, hne, hcop⟩ := coprime_triple_of_nonzero_poly hne0
  refine ⟨p, c, b, hne, hcop, fun j => ?_⟩
  apply mul_left_cancel₀ hg_ne
  rw [mul_zero]
  calc g * (p * D.Pj j + c * D.Cj j + b * D.Bj j)
      = (g * p) * D.Pj j + (g * c) * D.Cj j + (g * b) * D.Bj j := by ring
    _ = p0 * D.Pj j + c0 * D.Cj j + b0 * D.Bj j := by rw [← hp, ← hc, ← hb]
    _ = 0 := hsyz0 j

/-- **Theorem (`T4ABranch.p0Zero`):** If `detM = 0` with coprime syzygy `(0, c, b)`, then `D`
produces an explicit feasible vector `x : Fin 10 → ℚ` for `buildT4ARows .p0Zero`! -/
theorem table4_p0Zero_sat {c b : Fld[X]}
    (hne : c ≠ 0 ∨ b ≠ 0)
    (hcop : ∀ d : Fld[X], d ∣ c → d ∣ b → IsUnit d)
    (hsyz : ∀ j : Fin 3, c * D.Cj j + b * D.Bj j = 0)
    (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : ℕ)
    (hcLoD : 0 < cLoDen) (hcHiD : 0 < cHiDen) (hloGD : 0 < loGDen) (hhiGD : 0 < hiGDen)
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ))
    (hcHi : (D.W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (hloG : (loGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≥ (loGNum * N : ℤ))
    (hhiG : hiGNum < hiGDen → (hiGDen : ℤ) * ((D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ)) ≤ (hiGNum * N : ℤ)) :
    let rows := buildT4ARows .p0Zero cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
    ∃ x : Fin (t4aNumVars .p0Zero) → ℚ,
      (∀ j, 0 ≤ x j) ∧
      x ⟨0, by decide⟩ = (D.n0 : ℚ) / (N : ℚ) ∧ x ⟨1, by decide⟩ = (D.n1 : ℚ) / (N : ℚ) ∧
      x ⟨2, by decide⟩ = (D.n2 : ℚ) / (N : ℚ) ∧ x ⟨3, by decide⟩ = (D.n3 : ℚ) / (N : ℚ) ∧
      x ⟨4, by decide⟩ = (D.nt : ℚ) / (N : ℚ) ∧ x ⟨9, by decide⟩ = (D.W_F : ℚ) / (wY : ℚ) ∧
      (∀ r ∈ rows.1.toList, RowValid (t4aNumVars .p0Zero) r ∧ RowSatLe x r) ∧
      (∀ r ∈ rows.2.toList, RowValid (t4aNumVars .p0Zero) r ∧ RowSatEq x r) := by
  -- Extract K_j such that C_j = b * K_j and B_j = c * K_j!
  have hcb_cop : IsCoprime c b := isCoprime_of_forall_dvd_isUnit_poly hcop
  have hK : ∀ j : Fin 3, ∃ K : Fld[X], D.Cj j = b * K ∧ D.Bj j = c * K := by
    intro j
    have heq : c * D.Cj j = b * D.Bj j := by
      have h := hsyz j
      have hadd := congrArg (· + b * D.Bj j) h
      have hc := CharTwo.add_self_eq_zero (b * D.Bj j)
      linear_combination hadd - hc
    by_cases hb0 : b = 0
    · subst hb0
      have hc0 : c ≠ 0 := hne.resolve_right (by simp)
      rw [zero_mul] at heq
      have hC0 : D.Cj j = 0 := (mul_eq_zero.mp heq).resolve_left hc0
      -- c is a unit since gcd(c, 0) = 1!
      have hc_u : IsUnit c := hcop c dvd_rfl (dvd_zero c)
      obtain ⟨u, rfl⟩ := hc_u
      exact ⟨(u⁻¹ : Fld[X]ˣ) * D.Bj j, by rw [hC0, zero_mul], by rw [← mul_assoc, Units.mul_inv, one_mul]⟩
    · have hb_dvd : b ∣ D.Cj j := hcb_cop.symm.dvd_of_dvd_mul_left ⟨D.Bj j, heq⟩
      rcases hb_dvd with ⟨K, hK⟩
      refine ⟨K, hK, ?_⟩
      apply mul_left_cancel₀ hb0
      rw [← heq, hK]; ring
  let Kj : Fin 3 → Fld[X] := fun j => Classical.choose (hK j)
  have hKj : ∀ j : Fin 3, D.Cj j = b * Kj j ∧ D.Bj j = c * Kj j := fun j => Classical.choose_spec (hK j)
  let R : Fld[X] := b.comp (X ^ 2) + X * c.comp (X ^ 2)
  have hR_ne : R ≠ 0 := by
    intro h0; rcases (even_odd_pair_eq_zero_iff b c).mp h0 with ⟨rfl, rfl⟩
    exact hne.elim (fun h => h rfl) (fun h => h rfl)
  have hgj_eq : ∀ j : Fin 3, D.gj j = R * (Kj j).comp (X ^ 2) := by
    intro j; unfold gj R
    rw [(hKj j).1, (hKj j).2, mul_comp, mul_comp]; ring
  have hR_deg : R.natDegree ≤ D.W_F + 1 - 5 * wY := by
    have hg2 : D.gj 2 = R * (Kj 2).comp (X ^ 2) := hgj_eq 2
    have hK2_ne : (Kj 2).comp (X ^ 2) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hg2; exact D.g2_ne_zero hg2
    have hle : R.natDegree ≤ (D.gj 2).natDegree := by
      rw [hg2, natDegree_mul hR_ne hK2_ne]; omega
    exact hle.trans (D.natDegree_gj_le 2)
  let S : Fld[X] := ∑ j : Fin 3, sqrtPoly (Kj j) * D.P ^ j.val
  have hRS_sq : R * D.f1.eval D.P = (R * S) ^ 2 := by
    have hf1_eq : D.f1.eval D.P = R * S ^ 2 := by
      have hev_sum : D.f1.eval D.P = ∑ j : Fin 3, (C (D.gj j) * X ^ (2 * j.val)).eval D.P := by
        rw [D.f1_eq_sum]; exact map_sum (Polynomial.evalRingHom D.P) _ _
      rw [hev_sum]
      have hS2 : S ^ 2 = ∑ j : Fin 3, (Kj j).comp (X ^ 2) * D.P ^ (2 * j.val) := by
        dsimp only [S]
        have h2p : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
        have hfr : ∀ (f : Fin 3 → Fld[X]), (∑ j : Fin 3, f j) ^ 2 = ∑ j : Fin 3, f j ^ 2 := fun f => by
          rw [Fin.sum_univ_three, Fin.sum_univ_three]
          calc (f 0 + f 1 + f 2) ^ 2
              = f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 + 2 * (f 0 * f 1 + f 0 * f 2 + f 1 * f 2) := by ring
            _ = f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 := by rw [h2p]; ring
        rw [hfr]; apply Finset.sum_congr rfl; intro j _
        rw [mul_pow, sqrtPoly_sq, ← pow_mul, mul_comm j.val 2]
      rw [hS2, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
      rw [eval_mul, eval_C, eval_pow, eval_X, hgj_eq j]; ring
    rw [hf1_eq]; ring
  have hRS_ne : (R * S) ^ 2 ≠ 0 := by rw [← hRS_sq]; exact mul_ne_zero hR_ne D.f1_eval_P_ne_zero
  have hRS_deg : ((R * S) ^ 2).natDegree ≤ 2 * D.W_F - 6 * wY + 2 := by
    rw [← hRS_sq, natDegree_mul hR_ne D.f1_eval_P_ne_zero]
    have h1 := hR_deg; have h2 := D.natDegree_f1_eval_P_le; have h5 := D.hWF_lo
    omega
  have h2a_le : 2 * D.a1 + 4 * D.a2 + 6 * D.a3 ≤ 2 * D.W_F - 6 * wY + 2 := by
    have hdvd_even : ∀ i ∈ D.Az, (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i) ∣ (R * S) ^ 2 := by
      intro i hi
      set x0 := BinaryIRSProfile.domain i
      have hd1 : (X - C x0) ^ (2 * D.k i - 1) ∣ (R * S) ^ 2 := by
        rw [← hRS_sq]; exact dvd_mul_of_dvd_right (D.pow_dvd_f1_eval_P i hi) R
      have hrm1 : 2 * D.k i - 1 ≤ ((R * S) ^ 2).rootMultiplicity x0 :=
        (le_rootMultiplicity_iff hRS_ne).mpr hd1
      have hne_RS : R * S ≠ 0 := fun h0 => hRS_ne (by simp [h0])
      have hrm_ev : ((R * S) ^ 2).rootMultiplicity x0 = 2 * (R * S).rootMultiplicity x0 := by
        rw [sq, rootMultiplicity_mul (mul_ne_zero hne_RS hne_RS)]; omega
      have hrm2 : 2 * D.k i ≤ ((R * S) ^ 2).rootMultiplicity x0 := by omega
      exact (le_rootMultiplicity_iff hRS_ne).mp hrm2
    have hsum : 2 * D.a1 + 4 * D.a2 + 6 * D.a3 ≤ ∑ i ∈ D.Az, (2 * D.k i) := by
      have hrew : 2 * D.a1 + 4 * D.a2 + 6 * D.a3 =
          ∑ i ∈ D.Az, ((if D.k i = 1 then 2 else 0) + (if D.k i = 2 then 4 else 0) + (if 3 ≤ D.k i then 6 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
        unfold a1 a2 a3; ring
      rw [hrew]; apply Finset.sum_le_sum; intro i _; split_ifs <;> omega
    exact hsum.trans ((sum_ord_le_natDegree_of_dvd D.Az BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
      ((R * S) ^ 2) hRS_ne _ hdvd_even).trans hRS_deg)
  -- Assemble x : Fin 10 → ℚ and prove buildT4ARows .p0Zero satisfaction!
  let x : Fin 10 → ℚ := fun j =>
    match j.val with
    | 0 => (D.n0 : ℚ) / (N : ℚ) | 1 => (D.n1 : ℚ) / (N : ℚ)
    | 2 => (D.n2 : ℚ) / (N : ℚ) | 3 => (D.n3 : ℚ) / (N : ℚ)
    | 4 => (D.nt : ℚ) / (N : ℚ) | 5 => (D.a0 : ℚ) / (N : ℚ)
    | 6 => (D.a1 : ℚ) / (N : ℚ) | 7 => (D.a2 : ℚ) / (N : ℚ)
    | 8 => (D.a3 : ℚ) / (N : ℚ) | _ => (D.W_F : ℚ) / (wY : ℚ)
  refine ⟨x, fun j => by dsimp only [x]; split <;> positivity, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp only [t4aNumVars]
  have hBV := baseT4Rows_valid (nv := 10) (ic := 9) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD
  have hBS := D.baseT4Rows_sat (nv := 10) (ic := 9) (by omega) (by omega)
    cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen hcLoD hcHiD hloGD hhiGD x
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcLo hcHi hloG hhiG
  have hc_nn : (0 : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ) := by positivity
  have hN_eq : (N : ℚ) = 2 * (wY : ℚ) + 2 := by exact_mod_cast two_mul_wY_add_two.symm
  have hResB : D.n1 + 11 * D.n2 + 29 * D.n3 + 18 * D.nt ≤ 9 * D.W_F - 25 * wY + 5 :=
    D.resOrdU0_le_natDegree.trans D.natDegree_ResY_le
  constructor
  · intro r hr
    simp only [buildT4ARows, t4aNumVars, t4aStaticRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact ⟨hBV.1 r hr, hBS.1 r hr⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (1 : ℕ) < 10 by omega, show (2 : ℕ) < 10 by omega, show (3 : ℕ) < 10 by omega,
          show (4 : ℕ) < 10 by omega, show (9 : ℕ) < 10 by omega, ↓reduceDIte, ↓reduceIte, x, cI_mul_div_N, cH_mul_c_eq]
        have hResQ : (D.n1 : ℚ) + 11 * (D.n2 : ℚ) + 29 * (D.n3 : ℚ) + 18 * (D.nt : ℚ) ≤
            9 * (D.W_F : ℚ) - 25 * (wY : ℚ) + 5 := by
          have h25 : 25 * wY ≤ 9 * D.W_F := by have := D.hWF_lo; have := D.hwY_pos; omega
          have hZ : ((D.n1 + 11 * D.n2 + 29 * D.n3 + 18 * D.nt : ℕ) : ℤ) ≤ 9 * (D.W_F : ℤ) - 25 * (wY : ℤ) + 5 := by omega
          exact_mod_cast hZ
        push_cast; rw [hN_eq]; linarith
      · refine ⟨rowValid_mkStat _ _ _ (by intro e he; simp at he; rcases he with rfl | rfl | rfl | rfl <;> omega), ?_⟩
        rw [rowSatLe_mkStat_iff]
        simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          show (6 : ℕ) < 10 by omega, show (7 : ℕ) < 10 by omega, show (8 : ℕ) < 10 by omega,
          show (9 : ℕ) < 10 by omega, ↓reduceDIte, ↓reduceIte, x, cI_mul_div_N, cI_mul_c_eq]
        have h2aQ : 2 * (D.a1 : ℚ) + 4 * (D.a2 : ℚ) + 6 * (D.a3 : ℚ) ≤
            2 * (D.W_F : ℚ) - 6 * (wY : ℚ) + 2 := by
          have h6 : 6 * wY ≤ 2 * D.W_F := by have := D.hWF_lo; have := D.hwY_pos; omega
          have hZ : ((2 * D.a1 + 4 * D.a2 + 6 * D.a3 : ℕ) : ℤ) ≤ 2 * (D.W_F : ℤ) - 6 * (wY : ℤ) + 2 := by omega
          exact_mod_cast hZ
        push_cast; rw [hN_eq]; linarith
  · intro r hr
    simp only [buildT4ARows, t4aNumVars, t4aStaticRows, List.toList_toArray, List.append_nil] at hr
    exact ⟨hBV.2 r hr, hBS.2 r hr⟩

end KerD45Data

/-! ### Part 7: Exact `det M = 0, p ≠ 0, U(X, P) ≠ 0` Syzygy Package (`KerD45Syzygy`) -/

/-- Exact escape predicate: `U(X, P(X)) = p(X^2) P(X) + b(X^2) + X c(X^2) = 0` for a coprime
syzygy `(p, c, b)` of `M` with `p ≠ 0`. -/
def EscapeUZero (D : KerD45Data) : Prop :=
  ∃ p c b : Fld[X],
    p ≠ 0 ∧ (∀ d : Fld[X], d ∣ p → d ∣ c → d ∣ b → IsUnit d) ∧
    (∀ j : Fin 3, p * D.Pj j + c * D.Cj j + b * D.Bj j = 0) ∧
    p.comp (X ^ 2) * D.P + b.comp (X ^ 2) + X * c.comp (X ^ 2) = 0

/-- Full algebraic package for `det M = 0, p ≠ 0, U(X, P) ≠ 0`, shared by `P0`, `b1c1`, and `K ≠ 0`! -/
structure KerD45Syzygy (D : KerD45Data) where
  p : Fld[X]
  c : Fld[X]
  b : Fld[X]
  hp : p ≠ 0
  hcop : ∀ d : Fld[X], d ∣ p → d ∣ c → d ∣ b → IsUnit d
  hsyz : ∀ j : Fin 3, p * D.Pj j + c * D.Cj j + b * D.Bj j = 0
  hUP_ne : p.comp (X ^ 2) * D.P + b.comp (X ^ 2) + X * c.comp (X ^ 2) ≠ 0

namespace KerD45Syzygy

variable {D : KerD45Data} (S : KerD45Syzygy D)

noncomputable def R : Fld[X] := S.b.comp (X ^ 2) + X * S.c.comp (X ^ 2)
noncomputable def q : Fld[X] := S.b ^ 2 + X * S.c ^ 2
noncomputable def UP : Fld[X] := S.p.comp (X ^ 2) * D.P + S.R

lemma UP_eq : S.UP = S.p.comp (X ^ 2) * D.P + S.b.comp (X ^ 2) + X * S.c.comp (X ^ 2) := by
  unfold UP R; ring

lemma UP_ne_zero : S.UP ≠ 0 := by rw [S.UP_eq]; exact S.hUP_ne

lemma q_comp_X_sq : S.q.comp (X ^ 2) = S.R ^ 2 := by
  unfold q R
  have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
  rw [add_comp, pow_comp, mul_comp, X_comp, pow_comp]
  calc S.b.comp (X ^ 2) ^ 2 + X ^ 2 * S.c.comp (X ^ 2) ^ 2
      = S.b.comp (X ^ 2) ^ 2 + 2 * S.b.comp (X ^ 2) * (X * S.c.comp (X ^ 2)) + (X * S.c.comp (X ^ 2)) ^ 2 := by
        rw [h2]; ring
    _ = (S.b.comp (X ^ 2) + X * S.c.comp (X ^ 2)) ^ 2 := by ring

lemma q_eq_zero_iff : S.q = 0 ↔ S.R = 0 := by
  constructor
  · intro hq
    have h := S.q_comp_X_sq
    rw [hq, zero_comp] at h
    exact sq_eq_zero_iff.mp h.symm
  · intro hR
    have h := S.q_comp_X_sq
    rw [hR, zero_pow (by norm_num)] at h
    exact (comp_X_sq_eq_zero_iff S.q).mp h

lemma natDegree_q_eq_R : S.q.natDegree = S.R.natDegree := by
  have h := congrArg Polynomial.natDegree S.q_comp_X_sq
  rw [natDegree_comp_X_sq, natDegree_pow] at h
  omega

lemma natDegree_UP_le_max : S.UP.natDegree ≤ max (2 * S.p.natDegree + wY) S.R.natDegree := by
  unfold UP
  refine (natDegree_add_le _ _).trans (max_le_max ?_ le_rfl)
  refine natDegree_mul_le.trans ?_
  rw [natDegree_comp_X_sq]
  have := D.hPdeg
  omega

lemma natDegree_UP_le_of_le (h : S.R.natDegree ≤ 2 * S.p.natDegree + wY) :
    S.UP.natDegree ≤ 2 * S.p.natDegree + wY :=
  S.natDegree_UP_le_max.trans (max_le le_rfl h)

lemma natDegree_UP_eq_of_gt (h : 2 * S.p.natDegree + wY < S.R.natDegree) :
    S.UP.natDegree = S.R.natDegree := by
  unfold UP
  apply natDegree_add_eq_right_of_natDegree_lt
  refine lt_of_le_of_lt (natDegree_mul_le.trans ?_) h
  rw [natDegree_comp_X_sq]
  have := D.hPdeg
  omega

/-! #### Reduced minors `M21, M20, M10` and `Res_Y = H1 * Q2(X^2)^2` -/

private lemma minorExists (a b : Fin 3) :
    ∃ M : Fld[X],
      S.p * M = D.Cj a * D.Bj b + D.Cj b * D.Bj a ∧
      S.c * M = D.Pj a * D.Bj b + D.Pj b * D.Bj a ∧
      S.b * M = D.Pj a * D.Cj b + D.Pj b * D.Cj a := by
  have hsyz_a := S.hsyz a
  have hsyz_b := S.hsyz b
  set N : Fld[X] := D.Cj a * D.Bj b + D.Cj b * D.Bj a
  have hpc : S.p * (D.Pj a * D.Bj b + D.Pj b * D.Bj a) = S.c * N := by
    have h1 := congrArg (· * D.Bj b) hsyz_a
    have h2 := congrArg (· * D.Bj a) hsyz_b
    have hadd := congrArg₂ (· + ·) h1 h2
    simp only [zero_mul, add_zero] at hadd
    have hz1 := CharTwo.add_self_eq_zero (S.b * D.Bj a * D.Bj b)
    have hz2 := CharTwo.add_self_eq_zero (S.c * N)
    dsimp [N] at hz2 ⊢
    have hadd' := congrArg (· + S.c * (D.Cj a * D.Bj b + D.Cj b * D.Bj a)) hadd
    rw [zero_add] at hadd'
    linear_combination hadd' - hz1 - hz2
  have hpb : S.p * (D.Pj a * D.Cj b + D.Pj b * D.Cj a) = S.b * N := by
    have h1 := congrArg (· * D.Cj b) hsyz_a
    have h2 := congrArg (· * D.Cj a) hsyz_b
    have hadd := congrArg₂ (· + ·) h1 h2
    simp only [zero_mul, add_zero] at hadd
    have hz1 := CharTwo.add_self_eq_zero (S.c * D.Cj a * D.Cj b)
    have hz2 := CharTwo.add_self_eq_zero (S.b * N)
    dsimp [N] at hz2 ⊢
    have hadd' := congrArg (· + S.b * (D.Cj a * D.Bj b + D.Cj b * D.Bj a)) hadd
    rw [zero_add] at hadd'
    linear_combination hadd' - hz1 - hz2
  -- Show S.p ∣ N using S.hcop!
  have hp_dvd : S.p ∣ N := dvd_of_syzygy_coprime_poly S.hp S.hcop hpc hpb
  rcases hp_dvd with ⟨M, hM⟩
  refine ⟨M, hM.symm, ?_, ?_⟩
  · apply mul_left_cancel₀ S.hp
    calc S.p * (S.c * M) = S.c * (S.p * M) := by ring
      _ = S.c * N := by rw [← hM]
      _ = S.p * (D.Pj a * D.Bj b + D.Pj b * D.Bj a) := hpc.symm
  · apply mul_left_cancel₀ S.hp
    calc S.p * (S.b * M) = S.b * (S.p * M) := by ring
      _ = S.b * N := by rw [← hM]
      _ = S.p * (D.Pj a * D.Cj b + D.Pj b * D.Cj a) := hpb.symm

noncomputable def M21 : Fld[X] := Classical.choose (S.minorExists 2 1)
noncomputable def M20 : Fld[X] := Classical.choose (S.minorExists 2 0)
noncomputable def M10 : Fld[X] := Classical.choose (S.minorExists 1 0)

lemma p_mul_M21 : S.p * S.M21 = D.Cj 2 * D.Bj 1 + D.Cj 1 * D.Bj 2 := (Classical.choose_spec (S.minorExists 2 1)).1
lemma c_mul_M21 : S.c * S.M21 = D.Pj 2 * D.Bj 1 + D.Pj 1 * D.Bj 2 := (Classical.choose_spec (S.minorExists 2 1)).2.1
lemma b_mul_M21 : S.b * S.M21 = D.Pj 2 * D.Cj 1 + D.Pj 1 * D.Cj 2 := (Classical.choose_spec (S.minorExists 2 1)).2.2

lemma p_mul_M20 : S.p * S.M20 = D.Cj 2 * D.Bj 0 + D.Cj 0 * D.Bj 2 := (Classical.choose_spec (S.minorExists 2 0)).1
lemma c_mul_M20 : S.c * S.M20 = D.Pj 2 * D.Bj 0 + D.Pj 0 * D.Bj 2 := (Classical.choose_spec (S.minorExists 2 0)).2.1
lemma b_mul_M20 : S.b * S.M20 = D.Pj 2 * D.Cj 0 + D.Pj 0 * D.Cj 2 := (Classical.choose_spec (S.minorExists 2 0)).2.2

lemma p_mul_M10 : S.p * S.M10 = D.Cj 1 * D.Bj 0 + D.Cj 0 * D.Bj 1 := (Classical.choose_spec (S.minorExists 1 0)).1
lemma c_mul_M10 : S.c * S.M10 = D.Pj 1 * D.Bj 0 + D.Pj 0 * D.Bj 1 := (Classical.choose_spec (S.minorExists 1 0)).2.1
lemma b_mul_M10 : S.b * S.M10 = D.Pj 1 * D.Cj 0 + D.Pj 0 * D.Cj 1 := (Classical.choose_spec (S.minorExists 1 0)).2.2

lemma two_mul_natDegree_p_mul_M21_le : 2 * (S.p * S.M21).natDegree ≤ 2 * D.W_F - 8 * wY + 1 := by
  rw [S.p_mul_M21]
  have hC2 := D.two_mul_natDegree_Cj_le 2; have hB1 := D.two_mul_natDegree_Bj_le 1
  have hC1 := D.two_mul_natDegree_Cj_le 1; have hB2 := D.two_mul_natDegree_Bj_le 2
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have ht1 : 2 * (D.Cj 2 * D.Bj 1).natDegree ≤ 2 * D.W_F - 8 * wY + 1 := by
    have := natDegree_mul_le (p := D.Cj 2) (q := D.Bj 1); omega
  have ht2 : 2 * (D.Cj 1 * D.Bj 2).natDegree ≤ 2 * D.W_F - 8 * wY + 1 := by
    by_cases hB2z : D.Bj 2 = 0
    · simp [hB2z]
    · have h5le := D.five_wY_le_of_Bj2_ne_zero hB2z
      have := natDegree_mul_le (p := D.Cj 1) (q := D.Bj 2); omega
  have hadd := natDegree_add_le (D.Cj 2 * D.Bj 1) (D.Cj 1 * D.Bj 2)
  omega

lemma natDegree_p_add_M21_le (hM : S.M21 ≠ 0) : S.p.natDegree + S.M21.natDegree ≤ D.W_F - 4 * wY := by
  have h := S.two_mul_natDegree_p_mul_M21_le
  rw [natDegree_mul S.hp hM] at h; omega

lemma two_mul_natDegree_p_mul_M20_le : 2 * (S.p * S.M20).natDegree ≤ 2 * D.W_F - 6 * wY + 1 := by
  rw [S.p_mul_M20]
  have hC2 := D.two_mul_natDegree_Cj_le 2; have hB0 := D.two_mul_natDegree_Bj_le 0
  have hC0 := D.two_mul_natDegree_Cj_le 0; have hB2 := D.two_mul_natDegree_Bj_le 2
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have ht1 : 2 * (D.Cj 2 * D.Bj 0).natDegree ≤ 2 * D.W_F - 6 * wY + 1 := by
    have := natDegree_mul_le (p := D.Cj 2) (q := D.Bj 0); omega
  have ht2 : 2 * (D.Cj 0 * D.Bj 2).natDegree ≤ 2 * D.W_F - 6 * wY + 1 := by
    by_cases hB2z : D.Bj 2 = 0
    · simp [hB2z]
    · have h5le := D.five_wY_le_of_Bj2_ne_zero hB2z
      have := natDegree_mul_le (p := D.Cj 0) (q := D.Bj 2); omega
  have hadd := natDegree_add_le (D.Cj 2 * D.Bj 0) (D.Cj 0 * D.Bj 2)
  omega

lemma natDegree_p_add_M20_le (hM : S.M20 ≠ 0) : S.p.natDegree + S.M20.natDegree ≤ D.W_F - 3 * wY := by
  have h := S.two_mul_natDegree_p_mul_M20_le
  rw [natDegree_mul S.hp hM] at h; omega

lemma two_mul_natDegree_p_mul_M20_le_with_g2 :
    2 * (S.p * S.M20).natDegree ≤ D.W_F - wY + (D.gj 2).natDegree := by
  rw [S.p_mul_M20]
  have hB0 := D.two_mul_natDegree_Bj_le 0; have hC0 := D.two_mul_natDegree_Cj_le 0
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have ht1 : 2 * (D.Cj 2 * D.Bj 0).natDegree ≤ D.W_F - wY + (D.gj 2).natDegree := by
    by_cases hC2 : D.Cj 2 = 0
    · simp [hC2]
    · have hle : 2 * (D.Cj 2).natDegree ≤ (D.gj 2).natDegree :=
        two_mul_natDegree_le_even_odd (D.Cj 2) (D.Bj 2) hC2
      have := natDegree_mul_le (p := D.Cj 2) (q := D.Bj 0); omega
  have ht2 : 2 * (D.Cj 0 * D.Bj 2).natDegree ≤ D.W_F - wY + (D.gj 2).natDegree := by
    by_cases hB2 : D.Bj 2 = 0
    · simp [hB2]
    · have hle : 2 * (D.Bj 2).natDegree + 1 ≤ (D.gj 2).natDegree :=
        two_mul_natDegree_add_one_le_even_odd (D.Cj 2) (D.Bj 2) hB2
      have := natDegree_mul_le (p := D.Cj 0) (q := D.Bj 2); omega
  have hadd := natDegree_add_le (D.Cj 2 * D.Bj 0) (D.Cj 0 * D.Bj 2)
  omega

lemma two_mul_natDegree_p_mul_M10_le : 2 * (S.p * S.M10).natDegree ≤ 2 * D.W_F - 4 * wY + 1 := by
  rw [S.p_mul_M10]
  have hC1 := D.two_mul_natDegree_Cj_le 1; have hB0 := D.two_mul_natDegree_Bj_le 0
  have hC0 := D.two_mul_natDegree_Cj_le 0; have hB1 := D.two_mul_natDegree_Bj_le 1
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have h1 : (D.Cj 1 * D.Bj 0 + D.Cj 0 * D.Bj 1).natDegree ≤
      max ((D.Cj 1).natDegree + (D.Bj 0).natDegree) ((D.Cj 0).natDegree + (D.Bj 1).natDegree) :=
    (natDegree_add_le _ _).trans (max_le_max natDegree_mul_le natDegree_mul_le)
  have hle : (D.Cj 1).natDegree + (D.Bj 0).natDegree ≤ D.W_F - 2 * wY ∧
      (D.Cj 0).natDegree + (D.Bj 1).natDegree ≤ D.W_F - 2 * wY := by omega
  omega

lemma natDegree_p_add_M10_le (hM : S.M10 ≠ 0) : S.p.natDegree + S.M10.natDegree ≤ D.W_F - 2 * wY := by
  have h := S.two_mul_natDegree_p_mul_M10_le
  rw [natDegree_mul S.hp hM] at h; omega

lemma natDegree_R_mul_M21_le : (S.R * S.M21.comp (X ^ 2)).natDegree ≤ 2 * D.W_F - 7 * wY + 1 := by
  have hrew : S.R * S.M21.comp (X ^ 2) =
      (S.b * S.M21).comp (X ^ 2) + X * (S.c * S.M21).comp (X ^ 2) := by
    unfold R; rw [mul_comp, mul_comp]; ring
  rw [hrew]
  have hP2 := D.two_mul_natDegree_Pj_le 2; have hP1 := D.two_mul_natDegree_Pj_le 1
  have hC1 := D.two_mul_natDegree_Cj_le 1; have hC2 := D.two_mul_natDegree_Cj_le 2
  have hB1 := D.two_mul_natDegree_Bj_le 1; have hB2 := D.two_mul_natDegree_Bj_le 2
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hbM : 2 * (S.b * S.M21).natDegree ≤ 2 * D.W_F - 7 * wY + 1 := by
    rw [S.b_mul_M21]
    have h1 := (natDegree_add_le (D.Pj 2 * D.Cj 1) (D.Pj 1 * D.Cj 2)).trans (max_le_max natDegree_mul_le natDegree_mul_le)
    omega
  have hcM : 2 * (S.c * S.M21).natDegree ≤ 2 * D.W_F - 7 * wY := by
    rw [S.c_mul_M21]
    have ht1 : 2 * (D.Pj 2 * D.Bj 1).natDegree ≤ 2 * D.W_F - 7 * wY := by
      have := natDegree_mul_le (p := D.Pj 2) (q := D.Bj 1); omega
    have ht2 : 2 * (D.Pj 1 * D.Bj 2).natDegree ≤ 2 * D.W_F - 7 * wY := by
      by_cases hB2z : D.Bj 2 = 0
      · simp [hB2z]
      · have h5le := D.five_wY_le_of_Bj2_ne_zero hB2z
        have := natDegree_mul_le (p := D.Pj 1) (q := D.Bj 2); omega
    have hadd := natDegree_add_le (D.Pj 2 * D.Bj 1) (D.Pj 1 * D.Bj 2)
    omega
  have hle := natDegree_even_odd_le (S.b * S.M21) (S.c * S.M21)
  split_ifs at hle <;> omega

lemma natDegree_R_mul_M20_le : (S.R * S.M20.comp (X ^ 2)).natDegree ≤ 2 * D.W_F - 5 * wY + 1 := by
  have hrew : S.R * S.M20.comp (X ^ 2) =
      (S.b * S.M20).comp (X ^ 2) + X * (S.c * S.M20).comp (X ^ 2) := by
    unfold R; rw [mul_comp, mul_comp]; ring
  rw [hrew]
  have hP2 := D.two_mul_natDegree_Pj_le 2; have hP0 := D.two_mul_natDegree_Pj_le 0
  have hC0 := D.two_mul_natDegree_Cj_le 0; have hC2 := D.two_mul_natDegree_Cj_le 2
  have hB0 := D.two_mul_natDegree_Bj_le 0; have hB2 := D.two_mul_natDegree_Bj_le 2
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hbM : 2 * (S.b * S.M20).natDegree ≤ 2 * D.W_F - 5 * wY + 1 := by
    rw [S.b_mul_M20]
    have h1 := (natDegree_add_le (D.Pj 2 * D.Cj 0) (D.Pj 0 * D.Cj 2)).trans (max_le_max natDegree_mul_le natDegree_mul_le)
    omega
  have hcM : 2 * (S.c * S.M20).natDegree ≤ 2 * D.W_F - 5 * wY := by
    rw [S.c_mul_M20]
    have ht1 : 2 * (D.Pj 2 * D.Bj 0).natDegree ≤ 2 * D.W_F - 5 * wY := by
      have := natDegree_mul_le (p := D.Pj 2) (q := D.Bj 0); omega
    have ht2 : 2 * (D.Pj 0 * D.Bj 2).natDegree ≤ 2 * D.W_F - 5 * wY := by
      by_cases hB2z : D.Bj 2 = 0
      · simp [hB2z]
      · have h5le := D.five_wY_le_of_Bj2_ne_zero hB2z
        have := natDegree_mul_le (p := D.Pj 0) (q := D.Bj 2); omega
    have hadd := natDegree_add_le (D.Pj 2 * D.Bj 0) (D.Pj 0 * D.Bj 2)
    omega
  have hle := natDegree_even_odd_le (S.b * S.M20) (S.c * S.M20)
  split_ifs at hle <;> omega

lemma natDegree_UP_mul_M20_le : (S.UP * S.M20.comp (X ^ 2)).natDegree ≤ 2 * D.W_F - 5 * wY + 1 := by
  have hrew : S.UP * S.M20.comp (X ^ 2) =
      (S.p * S.M20).comp (X ^ 2) * D.P + S.R * S.M20.comp (X ^ 2) := by
    unfold UP; rw [mul_comp]; ring
  rw [hrew]
  refine (natDegree_add_le _ _).trans (max_le ?_ S.natDegree_R_mul_M20_le)
  refine natDegree_mul_le.trans ?_
  rw [natDegree_comp_X_sq]
  have h1 := S.two_mul_natDegree_p_mul_M20_le
  have hP := D.hPdeg; have h5 := D.hWF_lo; have hw := D.hwY_pos
  omega

lemma natDegree_R_mul_M10_le : (S.R * S.M10.comp (X ^ 2)).natDegree ≤ 2 * D.W_F - 3 * wY + 1 := by
  have hrew : S.R * S.M10.comp (X ^ 2) =
      (S.b * S.M10).comp (X ^ 2) + X * (S.c * S.M10).comp (X ^ 2) := by
    unfold R; rw [mul_comp, mul_comp]; ring
  rw [hrew]
  have hP1 := D.two_mul_natDegree_Pj_le 1; have hP0 := D.two_mul_natDegree_Pj_le 0
  have hC0 := D.two_mul_natDegree_Cj_le 0; have hC1 := D.two_mul_natDegree_Cj_le 1
  have hB0 := D.two_mul_natDegree_Bj_le 0; have hB1 := D.two_mul_natDegree_Bj_le 1
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hbM : 2 * (S.b * S.M10).natDegree ≤ 2 * D.W_F - 3 * wY + 1 := by
    rw [S.b_mul_M10]
    have h1 := (natDegree_add_le (D.Pj 1 * D.Cj 0) (D.Pj 0 * D.Cj 1)).trans (max_le_max natDegree_mul_le natDegree_mul_le)
    omega
  have hcM : 2 * (S.c * S.M10).natDegree ≤ 2 * D.W_F - 3 * wY := by
    rw [S.c_mul_M10]
    have h1 := (natDegree_add_le (D.Pj 1 * D.Bj 0) (D.Pj 0 * D.Bj 1)).trans (max_le_max natDegree_mul_le natDegree_mul_le)
    omega
  have hle := natDegree_even_odd_le (S.b * S.M10) (S.c * S.M10)
  split_ifs at hle <;> omega

noncomputable def H1 : Fld[X] :=
  S.p.comp (X ^ 2) ^ 4 * D.gj 0 + S.p.comp (X ^ 2) ^ 2 * S.R ^ 2 * D.gj 1 + S.R ^ 4 * D.gj 2

noncomputable def Q2 : Fld[X] := S.M20 ^ 2 + S.M21 * S.M10

noncomputable def P0 : Fld[X] := S.p ^ 4 * S.M10 + S.q ^ 2 * S.M21

/-- Exact char-2 factorization `Res_Y^{(5, 4)} = H_1(X) * Q_2(X^2)^2`! -/
theorem ResY_eq_H1_mul_Q2_sq : D.ResY = S.H1 * (S.Q2.comp (X ^ 2)) ^ 2 := by
  have hf0_eq : D.f0 =
      (C ((D.Pj 0).comp (X ^ 2)) + C ((D.Pj 1).comp (X ^ 2)) * X + C ((D.Pj 2).comp (X ^ 2)) * X ^ 2).comp (X ^ 2) +
      X * (C ((D.Bj 0).comp (X ^ 2)) + C ((D.Bj 1).comp (X ^ 2)) * X + C ((D.Bj 2).comp (X ^ 2)) * X ^ 2).comp (X ^ 2) := by
    rw [D.f0_eq_sum, Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, pow_zero, mul_one, zero_add, pow_one,
      add_comp, mul_comp, C_comp, X_comp, pow_comp]
    ring
  have hf1_eq : D.f1 = (C (D.gj 0) + C (D.gj 1) * X + C (D.gj 2) * X ^ 2).comp (X ^ 2) := by
    rw [D.f1_eq_sum, Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, pow_zero, mul_one,
      add_comp, mul_comp, C_comp, X_comp, pow_comp]
    ring
  haveI : CharP (RatFunc Fld) 2 :=
    charP_of_injective_algebraMap (IsFractionRing.injective Fld[X] (RatFunc Fld)) 2
  have hid := syzygy_res_factor_of_inj
    (algebraMap Fld[X] (RatFunc Fld)) (IsFractionRing.injective Fld[X] (RatFunc Fld))
    (D.Pj 0) (D.Pj 1) (D.Pj 2) (D.Cj 0) (D.Cj 1) (D.Cj 2) (D.Bj 0) (D.Bj 1) (D.Bj 2)
    S.p S.c S.b S.M21 S.M20 S.M10 S.hp D.g2_ne_zero
    (S.hsyz 0) (S.hsyz 1) (S.hsyz 2) S.p_mul_M21 S.p_mul_M20 S.p_mul_M10
  unfold KerD45Data.ResY H1 Q2 R
  rw [hf0_eq, hf1_eq]
  exact hid

lemma H1_ne_zero : S.H1 ≠ 0 := by
  intro h0; apply D.ResY_ne_zero; rw [S.ResY_eq_H1_mul_Q2_sq, h0, zero_mul]

lemma Q2_ne_zero : S.Q2 ≠ 0 := by
  intro h0; apply D.ResY_ne_zero; rw [S.ResY_eq_H1_mul_Q2_sq, h0, zero_comp, zero_pow (by norm_num), mul_zero]

lemma natDegree_H1_le_of_le (h : S.R.natDegree ≤ 2 * S.p.natDegree + wY) :
    S.H1.natDegree ≤ 8 * S.p.natDegree + D.W_F - wY + 1 := by
  unfold H1
  have hg0 := D.natDegree_gj_le 0; have hg1 := D.natDegree_gj_le 1; have hg2 := D.natDegree_gj_le 2
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hp_sq : (S.p.comp (X ^ 2)).natDegree = 2 * S.p.natDegree := natDegree_comp_X_sq S.p
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · refine natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) hg0) |>.trans (by omega)
  · refine natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) natDegree_pow_le)) hg1) |>.trans (by omega)
  · refine natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le hg2) |>.trans (by omega)

lemma natDegree_H1_le_of_gt (h : 2 * S.p.natDegree + wY < S.R.natDegree) :
    S.H1.natDegree ≤ 4 * S.R.natDegree + D.W_F - 5 * wY + 1 := by
  unfold H1
  have hg0 := D.natDegree_gj_le 0; have hg1 := D.natDegree_gj_le 1; have hg2 := D.natDegree_gj_le 2
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  have hp_sq : (S.p.comp (X ^ 2)).natDegree = 2 * S.p.natDegree := natDegree_comp_X_sq S.p
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · refine natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) hg0) |>.trans (by omega)
  · refine natDegree_mul_le.trans (Nat.add_le_add
      (natDegree_mul_le.trans (Nat.add_le_add (natDegree_pow_le.trans (by rw [hp_sq])) natDegree_pow_le)) hg1) |>.trans (by omega)
  · refine natDegree_mul_le.trans (Nat.add_le_add natDegree_pow_le hg2) |>.trans (by omega)

lemma two_mul_natDegree_p_add_Q2_le : 2 * S.p.natDegree + S.Q2.natDegree ≤ 2 * D.W_F - 6 * wY := by
  have heq : S.p ^ 2 * S.Q2 = (S.p * S.M20) ^ 2 + (S.p * S.M21) * (S.p * S.M10) := by unfold Q2; ring
  have hdeg : (S.p ^ 2 * S.Q2).natDegree = 2 * S.p.natDegree + S.Q2.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 S.hp) S.Q2_ne_zero, natDegree_pow]
  rw [← hdeg, heq]
  have h20 := S.two_mul_natDegree_p_mul_M20_le
  have h21 := S.two_mul_natDegree_p_mul_M21_le
  have h10 := S.two_mul_natDegree_p_mul_M10_le
  have h5 := D.hWF_lo; have hw := D.hwY_pos
  refine (natDegree_add_le _ _).trans (max_le (natDegree_pow_le.trans (by omega)) (natDegree_mul_le.trans (by omega)))

/-! #### Squarefree `D2 = gcd(p, q)` and `D1 = sqrtPoly D2` -/

noncomputable def D2 : Fld[X] := EuclideanDomain.gcd S.p S.q
noncomputable def D1 : Fld[X] := sqrtPoly S.D2

lemma D2_dvd_p : S.D2 ∣ S.p := EuclideanDomain.gcd_dvd_left S.p S.q
lemma D2_dvd_q : S.D2 ∣ S.q := EuclideanDomain.gcd_dvd_right S.p S.q

lemma D2_ne_zero : S.D2 ≠ 0 := fun h0 => S.hp (EuclideanDomain.gcd_eq_zero_iff.mp h0).1
lemma D1_ne_zero : S.D1 ≠ 0 := mt (sqrtPoly_eq_zero_iff S.D2).mp S.D2_ne_zero
lemma D1_sq : S.D1 ^ 2 = S.D2.comp (X ^ 2) := sqrtPoly_sq S.D2
lemma D1_natDegree : S.D1.natDegree = S.D2.natDegree := natDegree_sqrtPoly S.D2
lemma D2_natDegree_le_p : S.D2.natDegree ≤ S.p.natDegree := natDegree_le_of_dvd S.D2_dvd_p S.hp

lemma q_derivative_eq : S.q.derivative = S.c ^ 2 := by
  unfold q
  have hsq : ∀ f : Fld[X], (f ^ 2).derivative = 0 := fun f => (derivative_eq_zero_iff_sq (f ^ 2)).mpr ⟨f, rfl⟩
  rw [derivative_add, hsq S.b, zero_add, derivative_mul, derivative_X, one_mul, hsq S.c, mul_zero, add_zero]

lemma D2_coprime_c : IsCoprime S.D2 S.c := by
  refine isCoprime_of_forall_dvd_isUnit_poly fun d hd_D2 hd_c => ?_
  by_contra hnu
  have hd0 : d ≠ 0 := fun h0 => S.D2_ne_zero (zero_dvd_iff.mp (h0 ▸ hd_D2))
  obtain ⟨π, hπ_irr, hπ_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hd0
  have hπ_p : π ∣ S.p := hπ_dvd.trans (hd_D2.trans S.D2_dvd_p)
  have hπ_c : π ∣ S.c := hπ_dvd.trans hd_c
  have hπ_q : π ∣ S.q := hπ_dvd.trans (hd_D2.trans S.D2_dvd_q)
  have hπ_b2 : π ∣ S.b ^ 2 := by
    have hb2 : S.b ^ 2 = S.q + X * S.c ^ 2 := by
      unfold q; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hb2]
    exact dvd_add hπ_q (dvd_mul_of_dvd_right (dvd_pow hπ_c (by norm_num)) X)
  have hπ_b : π ∣ S.b := hπ_irr.prime.dvd_of_dvd_pow hπ_b2
  exact hπ_irr.not_isUnit (S.hcop π hπ_p hπ_c hπ_b)

lemma D2_coprime_q_derivative : IsCoprime S.D2 S.q.derivative := by
  rw [S.q_derivative_eq]; exact S.D2_coprime_c.pow_right

lemma D2_squarefree : Squarefree S.D2 := by
  intro r hr
  have hr2_q : r ^ 2 ∣ S.q := by rw [sq]; exact hr.trans S.D2_dvd_q
  rcases hr2_q with ⟨w, hw⟩
  have hr_q' : r ∣ S.q.derivative := by
    have hsq : (r ^ 2).derivative = 0 := (derivative_eq_zero_iff_sq (r ^ 2)).mpr ⟨r, rfl⟩
    rw [hw, derivative_mul, hsq, zero_mul, zero_add]
    exact dvd_mul_of_dvd_left ⟨r, sq r⟩ w.derivative
  have hr_D2 : r ∣ S.D2 := (dvd_mul_right r r).trans hr
  exact S.D2_coprime_q_derivative.isUnit_of_dvd' hr_D2 hr_q'

lemma D2_coprime_q_div_D2 : IsCoprime S.D2 (S.q / S.D2) := by
  refine isCoprime_of_forall_dvd_isUnit_poly fun d hd_D2 hd_qdiv => ?_
  have hd_q' : d ∣ S.q.derivative := by
    have hd2_q : d ^ 2 ∣ S.q := by
      rw [sq, ← EuclideanDomain.mul_div_cancel' S.D2_ne_zero S.D2_dvd_q]
      exact mul_dvd_mul hd_D2 hd_qdiv
    rcases hd2_q with ⟨w, hw⟩
    have hsq : (d ^ 2).derivative = 0 := (derivative_eq_zero_iff_sq (d ^ 2)).mpr ⟨d, rfl⟩
    rw [hw, derivative_mul, hsq, zero_mul, zero_add]
    exact dvd_mul_of_dvd_left ⟨d, sq d⟩ w.derivative
  exact S.D2_coprime_q_derivative.isUnit_of_dvd' hd_D2 hd_q'

lemma D2_rootMultiplicity_le_one (t : Fld) : S.D2.rootMultiplicity t ≤ 1 := by
  by_contra h
  have h2 : (X - C t) * (X - C t) ∣ S.D2 := by
    rw [← sq]; exact (pow_dvd_pow (X - C t) (by omega : 2 ≤ S.D2.rootMultiplicity t)).trans
      (pow_rootMultiplicity_dvd S.D2 t)
  have hu := S.D2_squarefree (X - C t) h2
  have h0 : (X - C t).natDegree = 0 := natDegree_eq_zero_of_isUnit hu
  rw [natDegree_X_sub_C] at h0; omega

lemma D1_rootMultiplicity_le_one (x : Fld) : S.D1.rootMultiplicity x ≤ 1 := by
  unfold D1; rw [rootMultiplicity_sqrtPoly S.D2 S.D2_ne_zero]; exact S.D2_rootMultiplicity_le_one (x ^ 2)

lemma dvd_of_sq_dvd_sq {a b : Fld[X]} (h : a ^ 2 ∣ b ^ 2) : a ∣ b :=
  dvd_of_sq_dvd_sq_poly h

lemma D1_dvd_R : S.D1 ∣ S.R := by
  apply dvd_of_sq_dvd_sq
  rw [S.D1_sq, ← S.q_comp_X_sq]
  rcases S.D2_dvd_q with ⟨w, hw⟩
  exact ⟨w.comp (X ^ 2), by rw [hw, mul_comp]⟩

lemma D1_dvd_UP : S.D1 ∣ S.UP := by
  unfold UP
  apply dvd_add
  · apply dvd_mul_of_dvd_left
    rcases S.D2_dvd_p with ⟨w, hw⟩
    refine ⟨S.D1 * w.comp (X ^ 2), ?_⟩
    rw [hw, mul_comp, ← S.D1_sq]; ring
  · exact S.D1_dvd_R

lemma D1_coprime_c_comp_X_sq : IsCoprime S.D1 (S.c.comp (X ^ 2)) := by
  rcases S.D2_coprime_c with ⟨u, v, huv⟩
  refine ⟨u.comp (X ^ 2) * S.D1, v.comp (X ^ 2), ?_⟩
  have hc := congrArg (fun f : Fld[X] => f.comp (X ^ 2)) huv
  simp only [add_comp, mul_comp, one_comp] at hc
  rw [← S.D1_sq] at hc
  calc u.comp (X ^ 2) * S.D1 * S.D1 + v.comp (X ^ 2) * S.c.comp (X ^ 2)
      = u.comp (X ^ 2) * S.D1 ^ 2 + v.comp (X ^ 2) * S.c.comp (X ^ 2) := by ring
    _ = 1 := hc

lemma D1_dvd_gj (j : Fin 3) : S.D1 ∣ D.gj j := by
  have heq : S.c.comp (X ^ 2) * D.gj j =
      S.p.comp (X ^ 2) * (D.Pj j).comp (X ^ 2) + S.R * (D.Bj j).comp (X ^ 2) := by
    have hsyz := congrArg (fun f : Fld[X] => f.comp (X ^ 2)) (S.hsyz j)
    simp only [add_comp, mul_comp, zero_comp] at hsyz
    have hadd := congrArg (· + S.c.comp (X ^ 2) * (D.Cj j).comp (X ^ 2)) hsyz
    have hz := CharTwo.add_self_eq_zero (S.c.comp (X ^ 2) * (D.Cj j).comp (X ^ 2))
    unfold KerD45Data.gj R
    linear_combination -hadd + hz
  have hd : S.D1 ∣ S.c.comp (X ^ 2) * D.gj j := by
    rw [heq]
    apply dvd_add
    · rcases S.D2_dvd_p with ⟨w, hw⟩
      exact ⟨S.D1 * w.comp (X ^ 2) * (D.Pj j).comp (X ^ 2), by rw [hw, mul_comp, ← S.D1_sq]; ring⟩
    · exact dvd_mul_of_dvd_left S.D1_dvd_R _
  exact S.D1_coprime_c_comp_X_sq.dvd_of_dvd_mul_left hd

lemma D1_pow5_dvd_H1 : S.D1 ^ 5 ∣ S.H1 := by
  have hD1_p : S.D1 ^ 2 ∣ S.p.comp (X ^ 2) := by
    rcases S.D2_dvd_p with ⟨w, hw⟩
    exact ⟨w.comp (X ^ 2), by rw [hw, mul_comp, S.D1_sq]⟩
  unfold H1
  apply dvd_add
  · apply dvd_add
    · have h1 : S.D1 ^ 8 ∣ S.p.comp (X ^ 2) ^ 4 := by
        rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul]; exact pow_dvd_pow_of_dvd hD1_p 4
      exact (pow_dvd_pow S.D1 (by omega : 5 ≤ 8)).trans (dvd_mul_of_dvd_left h1 _)
    · have h1 : S.D1 ^ 4 ∣ S.p.comp (X ^ 2) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]; exact pow_dvd_pow_of_dvd hD1_p 2
      have h2 : S.D1 ^ 2 ∣ S.R ^ 2 := pow_dvd_pow_of_dvd S.D1_dvd_R 2
      exact (pow_dvd_pow S.D1 (by omega : 5 ≤ 4 + 2)).trans
        (by rw [pow_add]; exact dvd_mul_of_dvd_left (mul_dvd_mul h1 h2) _)
  · rw [show (5 : ℕ) = 4 + 1 by rfl, pow_add, pow_one]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd S.D1_dvd_R 4) (S.D1_dvd_gj 2)

/-! #### Pointwise `U(x_i, y_i)`, shifted minors, and exact `U = 0` vs `U ≠ 0` local orders -/

noncomputable def U_eval (i : Idx) : Fld :=
  S.p.eval (BinaryIRSProfile.domain i ^ 2) * D.y i + S.R.eval (BinaryIRSProfile.domain i)

def isU0 (i : Idx) : Prop := S.U_eval i = 0

lemma UP_eval_eq (i : Idx) (hi : i ∈ D.Az) :
    S.UP.eval (BinaryIRSProfile.domain i) = S.U_eval i := by
  unfold UP U_eval
  rw [eval_add, eval_mul, eval_comp, eval_pow, eval_X, D.hagree i hi]

lemma dvd_UP_of_isU0 (i : Idx) (hi : i ∈ D.Az) (hU : S.isU0 i) :
    X - C (BinaryIRSProfile.domain i) ∣ S.UP := by
  rw [dvd_iff_isRoot, IsRoot, S.UP_eval_eq i hi]; exact hU

lemma D2_eval_eq_zero_iff (i : Idx) :
    S.D2.eval (BinaryIRSProfile.domain i ^ 2) = 0 ↔
      S.p.eval (BinaryIRSProfile.domain i ^ 2) = 0 ∧ S.isU0 i := by
  set x0 := BinaryIRSProfile.domain i
  set t0 := x0 ^ 2
  constructor
  · intro hD2
    have hd_p : S.p.eval t0 = 0 := by
      rcases S.D2_dvd_p with ⟨w, hw⟩; rw [hw, eval_mul, hD2, zero_mul]
    have hd_q : S.q.eval t0 = 0 := by
      rcases S.D2_dvd_q with ⟨w, hw⟩; rw [hw, eval_mul, hD2, zero_mul]
    have hR0 : S.R.eval x0 = 0 := by
      have h := congrArg (Polynomial.eval x0) S.q_comp_X_sq
      rw [eval_comp, eval_pow, eval_X, hd_q, eval_pow] at h
      exact sq_eq_zero_iff.mp h.symm
    exact ⟨hd_p, by unfold isU0 U_eval; rw [hd_p, zero_mul, hR0, add_zero]⟩
  · rintro ⟨hp0, hU0⟩
    have hR0 : S.R.eval x0 = 0 := by
      unfold isU0 U_eval at hU0; rw [hp0, zero_mul, zero_add] at hU0; exact hU0
    have hq0 : S.q.eval t0 = 0 := by
      have h := congrArg (Polynomial.eval x0) S.q_comp_X_sq
      rw [eval_comp, eval_pow, eval_X, eval_pow, hR0, zero_pow (by norm_num)] at h
      exact h
    have hdvd : X - C t0 ∣ S.D2 :=
      EuclideanDomain.dvd_gcd (dvd_iff_isRoot.mpr hp0) (dvd_iff_isRoot.mpr hq0)
    exact dvd_iff_isRoot.mp hdvd

/-- Shifted linear combination `Ush x0 y0 = b + x0 c + y0 p` whose value at `t0 = x0^2` is `U(x0, y0)`. -/
noncomputable def Ush (x0 y0 : Fld) : Fld[X] := S.b + C x0 * S.c + C y0 * S.p

lemma Ush_eval (x0 y0 : Fld) :
    (S.Ush x0 y0).eval (x0 ^ 2) = S.p.eval (x0 ^ 2) * y0 + S.R.eval x0 := by
  unfold Ush R
  simp only [eval_add, eval_mul, eval_C, eval_comp, eval_pow, eval_X]
  ring

lemma shifted_syzygy (x0 y0 : Fld) (j : Fin 3) :
    S.p * D.A0sh y0 j + S.c * D.A1sh x0 y0 j + S.Ush x0 y0 * D.Bsh y0 j = 0 := by
  have h0 := S.hsyz 0; have h1 := S.hsyz 1; have h2 := S.hsyz 2
  fin_cases j
  · simp only [KerD45Data.A0sh, KerD45Data.A1sh, KerD45Data.Bsh, Ush, Fin.val_zero]
    have hz1 := CharTwo.add_self_eq_zero (C y0 * S.p * (D.Bj 0 + C (y0 ^ 2) * D.Bj 1 + C (y0 ^ 4) * D.Bj 2))
    have hz2 := CharTwo.add_self_eq_zero (C x0 * S.c * (D.Bj 0 + C (y0 ^ 2) * D.Bj 1 + C (y0 ^ 4) * D.Bj 2))
    linear_combination h0 + C (y0 ^ 2) * h1 + C (y0 ^ 4) * h2 + hz1 + hz2
  · simp only [KerD45Data.A0sh, KerD45Data.A1sh, KerD45Data.Bsh, Ush, Fin.val_one]
    have hz1 := CharTwo.add_self_eq_zero (C y0 * S.p * D.Bj 1)
    have hz2 := CharTwo.add_self_eq_zero (C x0 * S.c * D.Bj 1)
    linear_combination h1 + hz1 + hz2
  · simp only [KerD45Data.A0sh, KerD45Data.A1sh, KerD45Data.Bsh, Ush, Fin.val_two]
    have hz1 := CharTwo.add_self_eq_zero (C y0 * S.p * D.Bj 2)
    have hz2 := CharTwo.add_self_eq_zero (C x0 * S.c * D.Bj 2)
    linear_combination h2 + hz1 + hz2

lemma pow_dvd_Bsh_U1 (i : Idx) (hU : ¬ S.isU0 i) (j : Fin 3) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (D.k i - j.val) ∣ D.Bsh (D.y i) j := by
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  set t0 := x0 ^ 2
  have hcop : IsCoprime ((X - C t0) ^ (D.k i - j.val)) (S.Ush x0 y0) := by
    apply IsCoprime.pow_left
    have hne : (S.Ush x0 y0).eval t0 ≠ 0 := by rw [S.Ush_eval]; exact hU
    exact (Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
  have hdvd : (X - C t0) ^ (D.k i - j.val) ∣ S.Ush x0 y0 * D.Bsh y0 j := by
    have hsyz := S.shifted_syzygy x0 y0 j
    have heq : S.Ush x0 y0 * D.Bsh y0 j = S.p * D.A0sh y0 j + S.c * D.A1sh x0 y0 j := by
      have hadd := congrArg (· + S.Ush x0 y0 * D.Bsh y0 j) hsyz
      have hz := CharTwo.add_self_eq_zero (S.Ush x0 y0 * D.Bsh y0 j)
      linear_combination -hadd + hz
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_right (D.local_shifted_ords i j).1 S.p)
      (dvd_mul_of_dvd_right (D.local_shifted_ords i j).2.1 S.c)
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem pow_dvd_ResY_U1 (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i)) ^ KerD45Data.resOrdU1 (D.k i) ∣ D.ResY := by
  simpa only [show (1 : ℕ) ≠ 0 by omega, ↓reduceIte] using
    D.pow_dvd_ResY_general i 1 (by omega) fun j => S.pow_dvd_Bsh_U1 i hU j

theorem pow_dvd_f1_eval_P_U1 (i : Idx) (hi : i ∈ D.Az) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i) ∣ D.f1.eval D.P := by
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  set t0 := x0 ^ 2
  have hP0 : D.P.eval x0 = y0 := D.hagree i hi
  have hm1 : biMultGE x0 y0 D.f1 (2 * D.k i) := by
    intro a b hab
    rw [D.shiftBi_f1_eq x0 y0, finset_sum_coeff, finset_sum_coeff]
    apply Finset.sum_eq_zero; intro j _
    rw [coeff_C_mul_X_pow]
    split_ifs with hb
    · rw [coeff_even_odd_pair]
      split_ifs with ha
      · exact shift_coeff_zero_of_pow_dvd _ t0 _ (D.local_shifted_ords i j).2.1 (a / 2) (by omega)
      · exact shift_coeff_zero_of_pow_dvd _ t0 _ (S.pow_dvd_Bsh_U1 i hU j) (a / 2) (by omega)
    · simp
  apply pow_dvd_of_shift_coeff_zero _ x0 _
  have hsh : (D.f1.eval D.P).comp (C x0 + X) =
      (shiftBi x0 y0 D.f1).eval (D.P.comp (C x0 + X) - C y0) := by
    unfold shiftBi
    rw [Polynomial.eval_comp, eval_add, eval_C, eval_X, add_sub_cancel]
    exact (Polynomial.eval_map_apply (f := Polynomial.compRingHom (C x0 + X)) (x := D.P) (p := D.f1)).symm
  rw [hsh]
  have hPsh_dvd : X ∣ (D.P.comp (C x0 + X) - C y0) := by
    rw [X_dvd_iff, coeff_sub, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_C, eval_X, add_zero,
      coeff_C_zero, hP0, sub_self]
  set Q := D.P.comp (C x0 + X) - C y0
  have hdvd_tot : X ^ (2 * D.k i) ∣ (shiftBi x0 y0 D.f1).eval Q := by
    rw [eval_eq_sum_range]
    apply Finset.dvd_sum; intro j _
    have hcj : X ^ (2 * D.k i - j) ∣ (shiftBi x0 y0 D.f1).coeff j := by
      simpa only [one_mul] using (biMultGE_iff_weightedOrdGE_one x0 y0 D.f1 (2 * D.k i)).mp hm1 j
    have hQj : X ^ j ∣ Q ^ j := pow_dvd_pow_of_dvd hPsh_dvd j
    exact (pow_dvd_pow X (show 2 * D.k i ≤ (2 * D.k i - j) + j by omega)).trans
      (by rw [pow_add]; exact mul_dvd_mul hcj hQj)
  exact X_pow_dvd_iff.mp hdvd_tot

noncomputable def M20sh (y0 : Fld) : Fld[X] := S.M20 + C (y0 ^ 2) * S.M21
noncomputable def M10sh (y0 : Fld) : Fld[X] := S.M10 + C (y0 ^ 4) * S.M21

lemma shifted_minor_identities (x0 y0 : Fld) :
    (S.p * S.M21 = D.A1sh x0 y0 2 * D.Bsh y0 1 + D.A1sh x0 y0 1 * D.Bsh y0 2 ∧
     S.c * S.M21 = D.A0sh y0 2 * D.Bsh y0 1 + D.A0sh y0 1 * D.Bsh y0 2 ∧
     S.Ush x0 y0 * S.M21 = D.A0sh y0 2 * D.A1sh x0 y0 1 + D.A0sh y0 1 * D.A1sh x0 y0 2) ∧
    (S.p * S.M20sh y0 = D.A1sh x0 y0 2 * D.Bsh y0 0 + D.A1sh x0 y0 0 * D.Bsh y0 2 ∧
     S.c * S.M20sh y0 = D.A0sh y0 2 * D.Bsh y0 0 + D.A0sh y0 0 * D.Bsh y0 2 ∧
     S.Ush x0 y0 * S.M20sh y0 = D.A0sh y0 2 * D.A1sh x0 y0 0 + D.A0sh y0 0 * D.A1sh x0 y0 2) ∧
    (S.p * S.M10sh y0 = D.A1sh x0 y0 1 * D.Bsh y0 0 + D.A1sh x0 y0 0 * D.Bsh y0 1 ∧
     S.c * S.M10sh y0 = D.A0sh y0 1 * D.Bsh y0 0 + D.A0sh y0 0 * D.Bsh y0 1 ∧
     S.Ush x0 y0 * S.M10sh y0 = D.A0sh y0 1 * D.A1sh x0 y0 0 + D.A0sh y0 0 * D.A1sh x0 y0 1) :=
  shifted_minor_identities_ring S.p S.c S.b (C x0) (C y0) (C (y0 ^ 2)) (C (y0 ^ 4))
    (D.Pj 0) (D.Pj 1) (D.Pj 2) (D.Cj 0) (D.Cj 1) (D.Cj 2) (D.Bj 0) (D.Bj 1) (D.Bj 2)
    S.M21 S.M20 S.M10
    S.p_mul_M21 S.c_mul_M21 S.b_mul_M21 S.p_mul_M20 S.c_mul_M20 S.b_mul_M20 S.p_mul_M10 S.c_mul_M10 S.b_mul_M10

private lemma pow_dvd_of_coprime_triple {x0 y0 t0 : Fld} {m : ℕ} {M : Fld[X]}
    (hp : (X - C t0) ^ m ∣ S.p * M) (hc : (X - C t0) ^ m ∣ S.c * M)
    (hu : (X - C t0) ^ m ∣ S.Ush x0 y0 * M) : (X - C t0) ^ m ∣ M := by
  have hne : S.p.eval t0 ≠ 0 ∨ S.c.eval t0 ≠ 0 ∨ (S.Ush x0 y0).eval t0 ≠ 0 := by
    by_contra hall; push Not at hall
    have hdp : X - C t0 ∣ S.p := dvd_iff_isRoot.mpr hall.1
    have hdc : X - C t0 ∣ S.c := dvd_iff_isRoot.mpr hall.2.1
    have hdu : X - C t0 ∣ S.Ush x0 y0 := dvd_iff_isRoot.mpr hall.2.2
    have hdb : X - C t0 ∣ S.b := by
      have hb_eq : S.b = S.Ush x0 y0 + C x0 * S.c + C y0 * S.p := by
        unfold Ush
        have z1 := CharTwo.add_self_eq_zero (C x0 * S.c)
        have z2 := CharTwo.add_self_eq_zero (C y0 * S.p)
        linear_combination -z1 - z2
      rw [hb_eq]; exact dvd_add (dvd_add hdu (dvd_mul_of_dvd_right hdc _)) (dvd_mul_of_dvd_right hdp _)
    have hu1 := S.hcop (X - C t0) hdp hdc hdb
    have hdeg := natDegree_eq_zero_of_isUnit hu1
    rw [natDegree_X_sub_C] at hdeg; omega
  rcases hne with h | h | h
  · exact ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left.dvd_of_dvd_mul_left hp
  · exact ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left.dvd_of_dvd_mul_left hc
  · exact ((Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp h)).pow_left.dvd_of_dvd_mul_left hu

/-- Exact local `T`-orders of `M21`, `M20sh`, `M10sh` at EVERY point `i : Idx` (both `U = 0` and `U ≠ 0`)! -/
theorem local_shifted_minor_ords (i : Idx) :
    let t0 : Fld := BinaryIRSProfile.domain i ^ 2
    let k := D.k i
    ((X - C t0) ^ (2 * k - 4) ∣ S.M21 ∧
     (X - C t0) ^ (if k ≤ 1 then 0 else 2 * k - 3) ∣ S.M20sh (D.y i) ∧
     (X - C t0) ^ (if k ≤ 1 then 0 else 2 * k - 2) ∣ S.M10sh (D.y i)) ∧
    (¬ S.isU0 i →
      (X - C t0) ^ (if k ≤ 1 then 0 else 2 * k - 3) ∣ S.M21 ∧
      (X - C t0) ^ (if k = 0 then 0 else if k = 1 then 1 else 2 * k - 2) ∣ S.M20sh (D.y i) ∧
      (X - C t0) ^ (if k = 0 then 0 else 2 * k - 1) ∣ S.M10sh (D.y i)) := by
  intro t0 k
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  have hloc0 := D.local_shifted_ords i 0
  have hloc1 := D.local_shifted_ords i 1
  have hloc2 := D.local_shifted_ords i 2
  have ⟨⟨hp21, hc21, hu21⟩, ⟨hp20, hc20, hu20⟩, ⟨hp10, hc10, hu10⟩⟩ := S.shifted_minor_identities x0 y0
  have hU_cop : ¬ S.isU0 i → ∀ m : ℕ, IsCoprime ((X - C t0) ^ m) (S.Ush x0 y0) := fun hU m => by
    apply IsCoprime.pow_left
    have hne : (S.Ush x0 y0).eval t0 ≠ 0 := by rw [S.Ush_eval]; exact hU
    exact (Polynomial.irreducible_X_sub_C t0).coprime_iff_not_dvd.mpr (mt dvd_iff_isRoot.mp hne)
  have hmul_ord : ∀ {a b m : ℕ} {f g : Fld[X]}, m ≤ a + b →
      (X - C t0) ^ a ∣ f → (X - C t0) ^ b ∣ g → (X - C t0) ^ m ∣ f * g := fun hle hf hg =>
    (pow_dvd_pow (X - C t0) hle).trans (by rw [pow_add]; exact mul_dvd_mul hf hg)
  have hu21_d : (X - C t0) ^ (if k ≤ 1 then 0 else 2 * k - 3) ∣ S.Ush x0 y0 * S.M21 := by
    rw [hu21]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc2.1 hloc1.2.1)
      (hmul_ord (by split_ifs <;> omega) hloc1.1 hloc2.2.1)
  have hu20_d : (X - C t0) ^ (if k = 0 then 0 else if k = 1 then 1 else 2 * k - 2) ∣ S.Ush x0 y0 * S.M20sh y0 := by
    rw [hu20]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc2.1 hloc0.2.1)
      (hmul_ord (by split_ifs <;> omega) hloc0.1 hloc2.2.1)
  have hu10_d : (X - C t0) ^ (if k = 0 then 0 else 2 * k - 1) ∣ S.Ush x0 y0 * S.M10sh y0 := by
    rw [hu10]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc1.1 hloc0.2.1)
      (hmul_ord (by split_ifs <;> omega) hloc0.1 hloc1.2.1)
  refine ⟨⟨?_, ?_, ?_⟩, fun hU => ⟨(hU_cop hU _).dvd_of_dvd_mul_left hu21_d,
    (hU_cop hU _).dvd_of_dvd_mul_left hu20_d, (hU_cop hU _).dvd_of_dvd_mul_left hu10_d⟩⟩
  · apply S.pow_dvd_of_coprime_triple (x0 := x0) (y0 := y0)
    · rw [hp21]; exact dvd_add (hmul_ord (by omega) hloc2.2.1 hloc1.2.2) (hmul_ord (by omega) hloc1.2.1 hloc2.2.2)
    · rw [hc21]; exact dvd_add (hmul_ord (by omega) hloc2.1 hloc1.2.2) (hmul_ord (by omega) hloc1.1 hloc2.2.2)
    · exact (pow_dvd_pow (X - C t0) (by split_ifs <;> omega)).trans hu21_d
  · apply S.pow_dvd_of_coprime_triple (x0 := x0) (y0 := y0)
    · rw [hp20]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc2.2.1 hloc0.2.2)
        (hmul_ord (by split_ifs <;> omega) hloc0.2.1 hloc2.2.2)
    · rw [hc20]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc2.1 hloc0.2.2)
        (hmul_ord (by split_ifs <;> omega) hloc0.1 hloc2.2.2)
    · exact (pow_dvd_pow (X - C t0) (by split_ifs <;> omega)).trans hu20_d
  · apply S.pow_dvd_of_coprime_triple (x0 := x0) (y0 := y0)
    · rw [hp10]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc1.2.1 hloc0.2.2)
        (hmul_ord (by split_ifs <;> omega) hloc0.2.1 hloc1.2.2)
    · rw [hc10]; exact dvd_add (hmul_ord (by split_ifs <;> omega) hloc1.1 hloc0.2.2)
        (hmul_ord (by split_ifs <;> omega) hloc0.1 hloc1.2.2)
    · exact (pow_dvd_pow (X - C t0) (by split_ifs <;> omega)).trans hu10_d

lemma Q2_eq_shifted (y0 : Fld) : S.Q2 = (S.M20sh y0) ^ 2 + S.M21 * S.M10sh y0 := by
  unfold Q2 M20sh M10sh
  have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
  have hz := CharTwo.add_self_eq_zero (C (y0 ^ 4) * S.M21 ^ 2)
  have hsq : C (y0 ^ 2) ^ 2 = (C (y0 ^ 4) : Fld[X]) := by rw [← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]
  calc S.M20 ^ 2 + S.M21 * S.M10
      = S.M20 ^ 2 + 2 * S.M20 * (C (y0 ^ 2) * S.M21) + C (y0 ^ 2) ^ 2 * S.M21 ^ 2 +
        S.M21 * S.M10 + C (y0 ^ 4) * S.M21 ^ 2 := by rw [h2, hsq]; linear_combination -hz
    _ = (S.M20 + C (y0 ^ 2) * S.M21) ^ 2 + S.M21 * (S.M10 + C (y0 ^ 4) * S.M21) := by ring

lemma P0_eq_shifted (y0 : Fld) :
    S.P0 = S.p ^ 4 * S.M10sh y0 + (S.q + C (y0 ^ 2) * S.p ^ 2) ^ 2 * S.M21 := by
  unfold P0 M10sh
  have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
  have hz := CharTwo.add_self_eq_zero (C (y0 ^ 4) * S.p ^ 4 * S.M21)
  have hsq : C (y0 ^ 2) ^ 2 = (C (y0 ^ 4) : Fld[X]) := by rw [← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]
  calc S.p ^ 4 * S.M10 + S.q ^ 2 * S.M21
      = S.p ^ 4 * S.M10 + C (y0 ^ 4) * S.p ^ 4 * S.M21 +
        (S.q ^ 2 + 2 * S.q * (C (y0 ^ 2) * S.p ^ 2) + C (y0 ^ 2) ^ 2 * S.p ^ 4) * S.M21 := by
          rw [h2, hsq]; linear_combination -hz
    _ = S.p ^ 4 * (S.M10 + C (y0 ^ 4) * S.M21) + (S.q + C (y0 ^ 2) * S.p ^ 2) ^ 2 * S.M21 := by ring

lemma pow_dvd_Q2_U0 (i : Idx) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (if D.k i ≤ 1 then 0 else 4 * D.k i - 6) ∣ S.Q2 := by
  rw [S.Q2_eq_shifted (D.y i)]
  have ⟨h21, h20, h10⟩ := (S.local_shifted_minor_ords i).1
  apply dvd_add
  · refine (pow_dvd_pow _ (show (if D.k i ≤ 1 then 0 else 4 * D.k i - 6) ≤
        2 * (if D.k i ≤ 1 then 0 else 2 * D.k i - 3) by split_ifs <;> omega)).trans ?_
    rw [show 2 * (if D.k i ≤ 1 then 0 else 2 * D.k i - 3) = (if D.k i ≤ 1 then 0 else 2 * D.k i - 3) * 2 by ring, pow_mul]
    exact pow_dvd_pow_of_dvd h20 2
  · refine (pow_dvd_pow _ (show (if D.k i ≤ 1 then 0 else 4 * D.k i - 6) ≤
        (2 * D.k i - 4) + (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) by split_ifs <;> omega)).trans ?_
    rw [pow_add]; exact mul_dvd_mul h21 h10

lemma pow_dvd_Q2_U1 (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^
      (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4) ∣ S.Q2 := by
  rw [S.Q2_eq_shifted (D.y i)]
  have ⟨h21, h20, h10⟩ := (S.local_shifted_minor_ords i).2 hU
  apply dvd_add
  · refine (pow_dvd_pow _ (show (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4) ≤
        2 * (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 2 * D.k i - 2) by split_ifs <;> omega)).trans ?_
    rw [show 2 * (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 2 * D.k i - 2) =
        (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 2 * D.k i - 2) * 2 by ring, pow_mul]
    exact pow_dvd_pow_of_dvd h20 2
  · refine (pow_dvd_pow _ (show (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4) ≤
        (if D.k i ≤ 1 then 0 else 2 * D.k i - 3) + (if D.k i = 0 then 0 else 2 * D.k i - 1) by split_ifs <;> omega)).trans ?_
    rw [pow_add]; exact mul_dvd_mul h21 h10

lemma pow_dvd_P0_U0 (i : Idx) (hU : S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) ∣ S.P0 := by
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  set t0 := x0 ^ 2
  rw [S.P0_eq_shifted y0]
  have ⟨h21, _, h10⟩ := (S.local_shifted_minor_ords i).1
  have hqsh : X - C t0 ∣ S.q + C (y0 ^ 2) * S.p ^ 2 := by
    rw [dvd_iff_isRoot, IsRoot, eval_add, eval_mul, eval_C, eval_pow]
    have hqval : S.q.eval t0 = S.R.eval x0 ^ 2 := by
      have h := congrArg (Polynomial.eval x0) S.q_comp_X_sq
      simpa [eval_comp, eval_pow, eval_X] using h
    rw [hqval]
    have h2 : (2 : Fld) = 0 := CharTwo.two_eq_zero
    calc S.R.eval x0 ^ 2 + y0 ^ 2 * S.p.eval t0 ^ 2
        = (S.p.eval t0 * y0 + S.R.eval x0) ^ 2 - 2 * (S.p.eval t0 * y0) * S.R.eval x0 := by ring
      _ = S.U_eval i ^ 2 := by rw [h2]; unfold U_eval; ring
      _ = 0 := by rw [hU]; ring
  apply dvd_add
  · exact dvd_mul_of_dvd_right h10 _
  · exact (pow_dvd_pow _ (show (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) ≤ 2 + (2 * D.k i - 4) by split_ifs <;> omega)).trans
      (by rw [pow_add]; exact mul_dvd_mul (pow_dvd_pow_of_dvd hqsh 2) h21)

lemma pow_dvd_P0_U1 (i : Idx) (hU : ¬ S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (if D.k i ≤ 1 then 0 else 2 * D.k i - 3) ∣ S.P0 := by
  rw [S.P0_eq_shifted (D.y i)]
  have ⟨h21, _, h10⟩ := (S.local_shifted_minor_ords i).2 hU
  apply dvd_add
  · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by split_ifs <;> omega)).trans h10) _
  · exact dvd_mul_of_dvd_right h21 _

lemma pow_dvd_H1_of_isU0 (i : Idx) (hU : S.isU0 i) :
    (X - C (BinaryIRSProfile.domain i)) ^ (2 * D.k i - 1) ∣ S.H1 := by
  set x0 := BinaryIRSProfile.domain i
  set y0 := D.y i
  set t0 := x0 ^ 2
  set Uy0 : Fld[X] := S.p.comp (X ^ 2) * C y0 + S.R
  have hUy0 : X - C x0 ∣ Uy0 := by
    rw [dvd_iff_isRoot, IsRoot]
    simp only [Uy0, eval_add, eval_mul, eval_comp, eval_pow, eval_X, eval_C]
    exact hU
  have hH1_rew : S.H1 =
      S.p.comp (X ^ 2) ^ 4 * (D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2) +
      S.p.comp (X ^ 2) ^ 2 * Uy0 ^ 2 * D.gj 1 + Uy0 ^ 4 * D.gj 2 := by
    have h2 : (2 : Fld[X]) = 0 := CharTwo.two_eq_zero
    have hR : S.R = Uy0 + S.p.comp (X ^ 2) * C y0 := by
      dsimp [Uy0]; rw [add_assoc, add_comm S.R, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have hR2 : S.R ^ 2 = Uy0 ^ 2 + S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2) := by
      rw [hR]; calc (Uy0 + S.p.comp (X ^ 2) * C y0) ^ 2
          = Uy0 ^ 2 + 2 * Uy0 * (S.p.comp (X ^ 2) * C y0) + S.p.comp (X ^ 2) ^ 2 * C y0 ^ 2 := by ring
        _ = Uy0 ^ 2 + S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2) := by rw [h2, ← map_pow]; ring
    have hR4 : S.R ^ 4 = Uy0 ^ 4 + S.p.comp (X ^ 2) ^ 4 * C (y0 ^ 4) := by
      calc S.R ^ 4 = (S.R ^ 2) ^ 2 := by ring
        _ = (Uy0 ^ 2 + S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2)) ^ 2 := by rw [hR2]
        _ = Uy0 ^ 4 + 2 * Uy0 ^ 2 * (S.p.comp (X ^ 2) ^ 2 * C (y0 ^ 2)) +
              S.p.comp (X ^ 2) ^ 4 * C (y0 ^ 2) ^ 2 := by ring
        _ = Uy0 ^ 4 + S.p.comp (X ^ 2) ^ 4 * C (y0 ^ 4) := by
              rw [h2, ← map_pow, show (y0 ^ 2) ^ 2 = y0 ^ 4 by ring]; ring
    unfold H1; rw [hR2, hR4]; ring
  have hgsh_dvd : ∀ (j : Fin 3) (gsh : Fld[X]),
      gsh = (D.A1sh x0 y0 j).comp (X ^ 2) + (X - C x0) * (D.Bsh y0 j).comp (X ^ 2) →
      (X - C x0) ^ (2 * D.k i - 1 - 2 * j.val) ∣ gsh := by
    intro j gsh hgsh
    rw [hgsh]
    have hloc := D.local_shifted_ords i j
    apply dvd_add
    · exact (pow_dvd_pow (X - C x0) (by omega : 2 * D.k i - 1 - 2 * j.val ≤ 2 * (D.k i - j.val))).trans
        ((pow_dvd_comp_X_sq_iff _ x0 _).mpr hloc.2.1)
    · by_cases hpos : 2 * D.k i - 1 - 2 * j.val = 0
      · rw [hpos, pow_zero]; exact one_dvd _
      · exact (pow_dvd_pow (X - C x0) (by omega : 2 * D.k i - 1 - 2 * j.val ≤ 1 + 2 * (D.k i - 1 - j.val))).trans
          (by rw [pow_add, pow_one]; exact mul_dvd_mul dvd_rfl ((pow_dvd_comp_X_sq_iff _ x0 _).mpr hloc.2.2))
  have hg0d : (X - C x0) ^ (2 * D.k i - 1) ∣ D.gj 0 + C (y0 ^ 2) * D.gj 1 + C (y0 ^ 4) * D.gj 2 := by
    simpa only [Fin.val_zero, mul_zero, Nat.sub_zero] using hgsh_dvd 0 _ (by
      simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_zero, add_comp, mul_comp, C_comp]; ring)
  have hg1d : (X - C x0) ^ (2 * D.k i - 3) ∣ D.gj 1 := by
    simpa only [Fin.val_one, mul_one, Nat.sub_sub] using hgsh_dvd 1 _ (by
      simp only [KerD45Data.gj, KerD45Data.A1sh, KerD45Data.Bsh, Fin.val_one, add_comp, mul_comp, C_comp]; ring)
  have hg2d : (X - C x0) ^ (2 * D.k i - 5) ∣ D.gj 2 := D.pow_dvd_g2_of_k i
  rw [hH1_rew]
  apply dvd_add
  · apply dvd_add
    · exact dvd_mul_of_dvd_right hg0d _
    · rw [mul_assoc]
      exact dvd_mul_of_dvd_right ((pow_dvd_pow (X - C x0) (by omega : 2 * D.k i - 1 ≤ 2 + (2 * D.k i - 3))).trans
        (by rw [pow_add]; exact mul_dvd_mul (pow_dvd_pow_of_dvd hUy0 2) hg1d)) _
  · exact (pow_dvd_pow (X - C x0) (by omega : 2 * D.k i - 1 ≤ 4 + (2 * D.k i - 5))).trans
      (by rw [pow_add]; exact mul_dvd_mul (pow_dvd_pow_of_dvd hUy0 4) hg2d)

/-! #### Shared `U = 0` point counts (`n1U, n2U, n3U, ntU, a1U, a2U, a3U`) and universal sum bounds -/

noncomputable def n1U : ℕ := by
  classical exact (Finset.univ.filter fun i : Idx => D.k i = 1 ∧ S.isU0 i).card
noncomputable def n2U : ℕ := by
  classical exact (Finset.univ.filter fun i : Idx => D.k i = 2 ∧ S.isU0 i).card
noncomputable def n3U : ℕ := by
  classical exact (Finset.univ.filter fun i : Idx => 3 ≤ D.k i ∧ S.isU0 i).card
noncomputable def ntU : ℕ := by
  classical exact ∑ i : Idx, if S.isU0 i then D.k i - 3 else 0
noncomputable def a1U : ℕ := by
  classical exact (D.Az.filter fun i : Idx => D.k i = 1 ∧ S.isU0 i).card
noncomputable def a2U : ℕ := by
  classical exact (D.Az.filter fun i : Idx => D.k i = 2 ∧ S.isU0 i).card
noncomputable def a3U : ℕ := by
  classical exact (D.Az.filter fun i : Idx => 3 ≤ D.k i ∧ S.isU0 i).card

attribute [irreducible] n1U n2U n3U ntU a1U a2U a3U

lemma U_counts_ineqs :
    S.n1U ≤ D.n1 ∧ S.n2U ≤ D.n2 ∧ S.n3U ≤ D.n3 ∧ S.ntU ≤ D.nt ∧
    S.a1U ≤ S.n1U ∧ S.a2U ≤ S.n2U ∧ S.a3U ≤ S.n3U ∧
    S.a1U ≤ D.a1 ∧ S.a2U ≤ D.a2 ∧ S.a3U ≤ D.a3 ∧
    D.a1 + S.n1U ≤ D.n1 + S.a1U ∧ D.a2 + S.n2U ≤ D.n2 + S.a2U ∧ D.a3 + S.n3U ≤ D.n3 + S.a3U := by
  classical
  have hsub : ∀ (U : Finset Idx) (hAU : D.Az ⊆ U) (p q : Idx → Prop) [DecidablePred p] [DecidablePred q],
      (D.Az.filter fun i => p i ∧ q i).card ≤ (U.filter fun i => p i ∧ q i).card ∧
      (D.Az.filter fun i => p i ∧ q i).card ≤ (D.Az.filter p).card ∧
      (U.filter fun i => p i ∧ q i).card ≤ (U.filter p).card ∧
      (D.Az.filter p).card + (U.filter fun i => p i ∧ q i).card ≤
        (U.filter p).card + (D.Az.filter fun i => p i ∧ q i).card := by
    intro U hAU p q _ _
    have h1 : (D.Az.filter fun i => p i ∧ q i) ⊆ (U.filter fun i => p i ∧ q i) :=
      Finset.filter_subset_filter _ hAU
    have h2 : (D.Az.filter fun i => p i ∧ q i) ⊆ (D.Az.filter p) := fun i hi => by
      simp only [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.1⟩
    have h3 : (U.filter fun i => p i ∧ q i) ⊆ (U.filter p) := fun i hi => by
      simp only [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.1⟩
    have h4 : (D.Az.filter p).card - (D.Az.filter fun i => p i ∧ q i).card ≤
        (U.filter p).card - (U.filter fun i => p i ∧ q i).card := by
      have hs1 : (D.Az.filter p) \ (D.Az.filter fun i => p i ∧ q i) ⊆
          (U.filter p) \ (U.filter fun i => p i ∧ q i) := fun i hi => by
        simp only [Finset.mem_sdiff, Finset.mem_filter] at hi ⊢
        exact ⟨⟨hAU hi.1.1, hi.1.2⟩, fun h => hi.2 ⟨hi.1.1, h.2⟩⟩
      have hc := Finset.card_le_card hs1
      rw [Finset.card_sdiff_of_subset h2, Finset.card_sdiff_of_subset h3] at hc
      exact hc
    have hc2 := Finset.card_le_card h2
    have hc3 := Finset.card_le_card h3
    exact ⟨Finset.card_le_card h1, hc2, hc3, by omega⟩
  have s1 := hsub Finset.univ (Finset.subset_univ _) (fun i => D.k i = 1) S.isU0
  have s2 := hsub Finset.univ (Finset.subset_univ _) (fun i => D.k i = 2) S.isU0
  have s3 := hsub Finset.univ (Finset.subset_univ _) (fun i => 3 ≤ D.k i) S.isU0
  have hnt : S.ntU ≤ D.nt := by
    unfold ntU KerD45Data.nt
    apply Finset.sum_le_sum; intro i _; split_ifs <;> omega
  unfold n1U n2U n3U a1U a2U a3U KerD45Data.n1 KerD45Data.n2 KerD45Data.n3 KerD45Data.a1 KerD45Data.a2 KerD45Data.a3
  refine ⟨?_, ?_, ?_, hnt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact s1.2.2.1
  · exact s2.2.2.1
  · exact s3.2.2.1
  · exact s1.1
  · exact s2.1
  · exact s3.1
  · exact s1.2.1
  · exact s2.2.1
  · exact s3.2.1
  · exact s1.2.2.2
  · exact s2.2.2.2
  · exact s3.2.2.2

lemma ResY_U_bound :
    (4 * D.n1 - 3 * S.n1U) + (16 * D.n2 - 5 * S.n2U) + (34 * D.n3 - 5 * S.n3U) + 18 * D.nt ≤
      D.ResY.natDegree := by
  classical
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
      (X - C (BinaryIRSProfile.domain i)) ^
        (if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i)) ∣ D.ResY := fun i _ => by
    split_ifs with hU
    · exact D.pow_dvd_ResY_U0 i
    · exact S.pow_dvd_ResY_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain
    BinaryIRSProfile.domain.injective D.ResY D.ResY_ne_zero _ hdvd
  have hgen : ∀ S0 : Finset Idx,
      4 * (S0.filter fun i => D.k i = 1).card + 16 * (S0.filter fun i => D.k i = 2).card +
      34 * (S0.filter fun i => 3 ≤ D.k i).card + 18 * ∑ i ∈ S0, (D.k i - 3) =
      (∑ i ∈ S0, (if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i))) +
      3 * (S0.filter fun i => D.k i = 1 ∧ S.isU0 i).card +
      5 * (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card +
      5 * (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card := by
    intro S0
    have hL : 4 * (S0.filter fun i => D.k i = 1).card + 16 * (S0.filter fun i => D.k i = 2).card +
        34 * (S0.filter fun i => 3 ≤ D.k i).card + 18 * ∑ i ∈ S0, (D.k i - 3) =
        ∑ i ∈ S0, ((if D.k i = 1 then 4 else 0) + (if D.k i = 2 then 16 else 0) +
          (if 3 ≤ D.k i then 34 else 0) + 18 * (D.k i - 3)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, smul_eq_mul]; ring
    have hR : (∑ i ∈ S0, (if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i))) +
        3 * (S0.filter fun i => D.k i = 1 ∧ S.isU0 i).card +
        5 * (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card +
        5 * (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card =
        ∑ i ∈ S0, ((if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i)) +
          (if D.k i = 1 ∧ S.isU0 i then 3 else 0) + (if D.k i = 2 ∧ S.isU0 i then 5 else 0) +
          (if 3 ≤ D.k i ∧ S.isU0 i then 5 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, smul_eq_mul]; ring
    rw [hL, hR]; apply Finset.sum_congr rfl; intro i _; unfold KerD45Data.resOrdU0 KerD45Data.resOrdU1
    by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
  have heq : 4 * D.n1 + 16 * D.n2 + 34 * D.n3 + 18 * D.nt =
      (∑ i : Idx, (if S.isU0 i then KerD45Data.resOrdU0 (D.k i) else KerD45Data.resOrdU1 (D.k i))) +
      3 * S.n1U + 5 * S.n2U + 5 * S.n3U := by
    unfold n1U n2U n3U KerD45Data.n1 KerD45Data.n2 KerD45Data.n3 KerD45Data.nt
    exact hgen Finset.univ
  have hi := S.U_counts_ineqs
  have := hi.1; have := hi.2.1; have := hi.2.2.1
  omega

lemma f1_eval_P_U_bound :
    (2 * D.a1 - S.a1U) + (4 * D.a2 - S.a2U) + (6 * D.a3 - S.a3U) ≤ D.W_F - wY + 1 := by
  classical
  have hdvd : ∀ i ∈ D.Az,
      (X - C (BinaryIRSProfile.domain i)) ^ (if S.isU0 i then 2 * D.k i - 1 else 2 * D.k i) ∣ D.f1.eval D.P :=
    fun i hi => by
      split_ifs with hU
      · exact D.pow_dvd_f1_eval_P i hi
      · exact S.pow_dvd_f1_eval_P_U1 i hi hU
  have hle := (sum_ord_le_natDegree_of_dvd D.Az BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    (D.f1.eval D.P) D.f1_eval_P_ne_zero _ hdvd).trans D.natDegree_f1_eval_P_le
  have hL : 2 * D.a1 + 4 * D.a2 + 6 * D.a3 =
      ∑ i ∈ D.Az, ((if D.k i = 1 then 2 else 0) + (if D.k i = 2 then 4 else 0) + (if 3 ≤ D.k i then 6 else 0)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    unfold KerD45Data.a1 KerD45Data.a2 KerD45Data.a3; ring
  have hR : (∑ i ∈ D.Az, (if S.isU0 i then 2 * D.k i - 1 else 2 * D.k i)) + S.a1U + S.a2U + S.a3U =
      ∑ i ∈ D.Az, ((if S.isU0 i then 2 * D.k i - 1 else 2 * D.k i) +
        (if D.k i = 1 ∧ S.isU0 i then 1 else 0) + (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
        (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
    unfold a1U a2U a3U; ring
  have hcmp : 2 * D.a1 + 4 * D.a2 + 6 * D.a3 ≤
      (∑ i ∈ D.Az, (if S.isU0 i then 2 * D.k i - 1 else 2 * D.k i)) + S.a1U + S.a2U + S.a3U := by
    rw [hL, hR]; apply Finset.sum_le_sum; intro i _
    by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
  have hi := S.U_counts_ineqs
  have := hi.2.2.2.2.2.2.2.1; have := hi.2.2.2.2.2.2.2.2.1; have := hi.2.2.2.2.2.2.2.2.2.1
  omega

lemma aU_sum_le_UP : S.a1U + S.a2U + S.a3U ≤ S.UP.natDegree := by
  classical
  have hdvd : ∀ i ∈ D.Az, (X - C (BinaryIRSProfile.domain i)) ^ (if 1 ≤ D.k i ∧ S.isU0 i then 1 else 0) ∣ S.UP :=
    fun i hi => by
      split_ifs with h
      · rw [pow_one]; exact S.dvd_UP_of_isU0 i hi h.2
      · rw [pow_zero]; exact one_dvd _
  have hle := sum_ord_le_natDegree_of_dvd D.Az BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    S.UP S.UP_ne_zero _ hdvd
  have hsum : S.a1U + S.a2U + S.a3U = ∑ i ∈ D.Az, (if 1 ≤ D.k i ∧ S.isU0 i then 1 else 0) := by
    have hrew : S.a1U + S.a2U + S.a3U =
        ∑ i ∈ D.Az, ((if D.k i = 1 ∧ S.isU0 i then 1 else 0) + (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
          (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        smul_eq_mul, mul_one]
      unfold a1U a2U a3U; ring
    rw [hrew]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
  omega

lemma H1_U_bound : S.n1U + 3 * S.n2U + 5 * S.n3U + 2 * S.ntU ≤ S.H1.natDegree := by
  classical
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
      (X - C (BinaryIRSProfile.domain i)) ^ (if S.isU0 i then 2 * D.k i - 1 else 0) ∣ S.H1 := fun i _ => by
    split_ifs with hU
    · exact S.pow_dvd_H1_of_isU0 i hU
    · rw [pow_zero]; exact one_dvd _
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ BinaryIRSProfile.domain BinaryIRSProfile.domain.injective
    S.H1 S.H1_ne_zero _ hdvd
  have hsum : S.n1U + 3 * S.n2U + 5 * S.n3U + 2 * S.ntU =
      ∑ i : Idx, (if S.isU0 i then 2 * D.k i - 1 else 0) := by
    have hgen : ∀ S0 : Finset Idx,
        (S0.filter fun i => D.k i = 1 ∧ S.isU0 i).card + 3 * (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card +
        5 * (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card + 2 * ∑ i ∈ S0, (if S.isU0 i then D.k i - 3 else 0) =
        ∑ i ∈ S0, (if S.isU0 i then 2 * D.k i - 1 else 0) := by
      intro S0
      have hrew : (S0.filter fun i => D.k i = 1 ∧ S.isU0 i).card + 3 * (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card +
          5 * (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card + 2 * ∑ i ∈ S0, (if S.isU0 i then D.k i - 3 else 0) =
          ∑ i ∈ S0, ((if D.k i = 1 ∧ S.isU0 i then 1 else 0) + (if D.k i = 2 ∧ S.isU0 i then 3 else 0) +
            (if 3 ≤ D.k i ∧ S.isU0 i then 5 else 0) + 2 * (if S.isU0 i then D.k i - 3 else 0)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, smul_eq_mul, mul_one]; ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _
      by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
    unfold n1U n2U n3U ntU; exact hgen Finset.univ
  omega

lemma Q2_U_bound :
    (D.n1 - S.n1U) + (4 * D.n2 - 2 * S.n2U) + (8 * D.n3 - 2 * S.n3U) + 4 * D.nt ≤ S.Q2.natDegree := by
  classical
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
      (X - C (BinaryIRSProfile.domain i ^ 2)) ^
        (if S.isU0 i then (if D.k i ≤ 1 then 0 else 4 * D.k i - 6)
         else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4)) ∣ S.Q2 := fun i _ => by
    by_cases hU : S.isU0 i
    · simp only [hU, ↓reduceIte]; exact S.pow_dvd_Q2_U0 i
    · simp only [hU, ↓reduceIte]; exact S.pow_dvd_Q2_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i : Idx => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective S.Q2 S.Q2_ne_zero _ hdvd
  have hgen : ∀ S0 : Finset Idx,
      (S0.filter fun i => D.k i = 1).card + 4 * (S0.filter fun i => D.k i = 2).card +
      8 * (S0.filter fun i => 3 ≤ D.k i).card + 4 * ∑ i ∈ S0, (D.k i - 3) =
      (∑ i ∈ S0, (if S.isU0 i then (if D.k i ≤ 1 then 0 else 4 * D.k i - 6)
         else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4))) +
      (S0.filter fun i => D.k i = 1 ∧ S.isU0 i).card +
      2 * (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card +
      2 * (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card := by
    intro S0
    have hL : (S0.filter fun i => D.k i = 1).card + 4 * (S0.filter fun i => D.k i = 2).card +
        8 * (S0.filter fun i => 3 ≤ D.k i).card + 4 * ∑ i ∈ S0, (D.k i - 3) =
        ∑ i ∈ S0, ((if D.k i = 1 then 1 else 0) + (if D.k i = 2 then 4 else 0) +
          (if 3 ≤ D.k i then 8 else 0) + 4 * (D.k i - 3)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, smul_eq_mul, mul_one]; ring
    have hR : (∑ i ∈ S0, (if S.isU0 i then (if D.k i ≤ 1 then 0 else 4 * D.k i - 6)
         else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4))) +
        (S0.filter fun i => D.k i = 1 ∧ S.isU0 i).card +
        2 * (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card +
        2 * (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card =
        ∑ i ∈ S0, ((if S.isU0 i then (if D.k i ≤ 1 then 0 else 4 * D.k i - 6)
           else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4)) +
          (if D.k i = 1 ∧ S.isU0 i then 1 else 0) + (if D.k i = 2 ∧ S.isU0 i then 2 else 0) +
          (if 3 ≤ D.k i ∧ S.isU0 i then 2 else 0)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
        add_zero, Finset.sum_const, smul_eq_mul, mul_one]; ring
    rw [hL, hR]; apply Finset.sum_congr rfl; intro i _
    by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
  have heq : D.n1 + 4 * D.n2 + 8 * D.n3 + 4 * D.nt =
      (∑ i : Idx, (if S.isU0 i then (if D.k i ≤ 1 then 0 else 4 * D.k i - 6)
         else (if D.k i = 0 then 0 else if D.k i = 1 then 1 else 4 * D.k i - 4))) +
      S.n1U + 2 * S.n2U + 2 * S.n3U := by
    unfold n1U n2U n3U KerD45Data.n1 KerD45Data.n2 KerD45Data.n3 KerD45Data.nt
    exact hgen Finset.univ
  have hi := S.U_counts_ineqs
  have := hi.1; have := hi.2.1; have := hi.2.2.1
  omega

lemma P0_U_bound (hP0 : S.P0 ≠ 0) :
    (D.n2 + S.n2U) + (3 * D.n3 + S.n3U) + 2 * D.nt ≤ S.P0.natDegree := by
  classical
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
      (X - C (BinaryIRSProfile.domain i ^ 2)) ^
        (if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 2)
         else (if D.k i ≤ 1 then 0 else 2 * D.k i - 3)) ∣ S.P0 := fun i _ => by
    by_cases hU : S.isU0 i
    · simp only [hU, ↓reduceIte]; exact S.pow_dvd_P0_U0 i hU
    · simp only [hU, ↓reduceIte]; exact S.pow_dvd_P0_U1 i hU
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i : Idx => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective S.P0 hP0 _ hdvd
  have hsum : (D.n2 + S.n2U) + (3 * D.n3 + S.n3U) + 2 * D.nt =
      ∑ i : Idx, (if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 2)
         else (if D.k i ≤ 1 then 0 else 2 * D.k i - 3)) := by
    have hgen : ∀ S0 : Finset Idx,
        ((S0.filter fun i => D.k i = 2).card + (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card) +
        (3 * (S0.filter fun i => 3 ≤ D.k i).card + (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card) +
        2 * ∑ i ∈ S0, (D.k i - 3) =
        ∑ i ∈ S0, (if S.isU0 i then (if D.k i ≤ 1 then 0 else 2 * D.k i - 2)
           else (if D.k i ≤ 1 then 0 else 2 * D.k i - 3)) := by
      intro S0
      have hrew : ((S0.filter fun i => D.k i = 2).card + (S0.filter fun i => D.k i = 2 ∧ S.isU0 i).card) +
          (3 * (S0.filter fun i => 3 ≤ D.k i).card + (S0.filter fun i => 3 ≤ D.k i ∧ S.isU0 i).card) +
          2 * ∑ i ∈ S0, (D.k i - 3) =
          ∑ i ∈ S0, ((if D.k i = 2 then 1 else 0) + (if D.k i = 2 ∧ S.isU0 i then 1 else 0) +
            (if 3 ≤ D.k i then 3 else 0) + (if 3 ≤ D.k i ∧ S.isU0 i then 1 else 0) + 2 * (D.k i - 3)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, smul_eq_mul, mul_one]; ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _
      by_cases hU : S.isU0 i <;> simp only [hU, and_true, and_false, ↓reduceIte] <;> split_ifs <;> omega
    unfold n2U n3U KerD45Data.n2 KerD45Data.n3 KerD45Data.nt; exact hgen Finset.univ
  omega

lemma pM10_bound_of_M21_zero (hM21 : S.M21 = 0) (hM10 : S.M10 ≠ 0) :
    2 * D.n2 + 4 * D.n3 + 2 * D.nt ≤ D.W_F - 2 * wY := by
  have hdvd : ∀ i ∈ (Finset.univ : Finset Idx),
      (X - C (BinaryIRSProfile.domain i ^ 2)) ^ (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) ∣ S.p * S.M10 := by
    intro i _
    have hM10sh : S.M10sh (D.y i) = S.M10 := by unfold M10sh; rw [hM21, mul_zero, add_zero]
    rw [← hM10sh]
    exact dvd_mul_of_dvd_right (S.local_shifted_minor_ords i).1.2.2 S.p
  have hle := sum_ord_le_natDegree_of_dvd Finset.univ (fun i : Idx => BinaryIRSProfile.domain i ^ 2)
    domain_sq_injective (S.p * S.M10) (mul_ne_zero S.hp hM10) _ hdvd
  have hsum : 2 * D.n2 + 4 * D.n3 + 2 * D.nt =
      ∑ i : Idx, (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) := by
    have hgen : ∀ S0 : Finset Idx,
        2 * (S0.filter fun i => D.k i = 2).card + 4 * (S0.filter fun i => 3 ≤ D.k i).card +
        2 * ∑ i ∈ S0, (D.k i - 3) = ∑ i ∈ S0, (if D.k i ≤ 1 then 0 else 2 * D.k i - 2) := by
      intro S0
      have hrew : 2 * (S0.filter fun i => D.k i = 2).card + 4 * (S0.filter fun i => 3 ≤ D.k i).card +
          2 * ∑ i ∈ S0, (D.k i - 3) =
          ∑ i ∈ S0, ((if D.k i = 2 then 2 else 0) + (if 3 ≤ D.k i then 4 else 0) + 2 * (D.k i - 3)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, smul_eq_mul, mul_one]; ring
      rw [hrew]; apply Finset.sum_congr rfl; intro i _; split_ifs <;> omega
    unfold KerD45Data.n2 KerD45Data.n3 KerD45Data.nt; exact hgen Finset.univ
  have hdeg := S.natDegree_p_add_M10_le hM10
  rw [← natDegree_mul S.hp hM10] at hdeg
  omega

end KerD45Syzygy

end B6401Table4Common
end ProximityPrize.SubmissionBinaryLower
