import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart2
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

end KerD45Data
end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
