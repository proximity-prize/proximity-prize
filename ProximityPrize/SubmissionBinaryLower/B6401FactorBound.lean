import ProximityPrize.SubmissionBinaryLower.B6401PointSurplus
import ProximityPrize.SubmissionBinaryLower.B6401Table4Common
import ProximityPrize.SubmissionBinaryLower.B6401Table4NonK
import ProximityPrize.SubmissionBinaryLower.B6401Table4K
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

/-!
# Single-Factor Line Bounds (`deg_R = 1`, `deg_R = 2`) and `ScalarListBound 10000000`

Connects all 4 certificate tables (Tables 1, 2, 3/2A/2B via `B6401PointSurplus`, and all 120
Table 4 branches via `B6401Table4Common` / `B6401Table4NonK` / `B6401Table4K`) to the unified
quotient-surplus bridge (`B6401QuotBridge`):
1. `baseT4Rows_transport` and `table4_surplus_from_bucket`: exact transport of Table 4 feasible
   vectors from `[T4_START, T4_END]` into any matched grid bin/bucket (`SINGLE` or `STD5`).
2. `deg1_factor_card_le`: unified `deg_R = 1` line bound for `q₀ ∈ {1, 2}` covering both Table 1
   and all 120 Table 4 branches (including global `3 × 3` matrix syzygy and `U_Z(z, X, P z) = 0`
   escape via `card_le_of_biPoly_pow`).
3. `deg2_factor_card_le`: unified `deg_R = 2, f1 ≠ 0` line bound (`q₀ = 1`) covering Tables 2, 3,
   2A, 2B.
4. `evalContact_contactDeriv`: char-2 chain rule `evalContact (contactDeriv F) P = (evalContact F P).derivative`.
5. `scalarListBound_6401`: `ScalarListBound 10000000` via `dy = 0, D_ZF = 0` interpolation and
   `card_le_of_degZ_zero_surplus`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401FactorBound

open Polynomial B6401Params B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open B6401KerDOrders B6401KerD2 B6401FarkasVerifier B6401HybridP64 B6401IntFarkas
open B6401IntSmallCerts B6401T4Rows B6401T4Grid
open B6401CertsT1 B6401CertsT2 B6401CertsT3 B6401CertsT4a B6401CertsT4b1 B6401CertsT4b2
open B6401SmallAlg B6401ResLineOrd B6401QuotBridge B6401PointSurplus
open B6401Table4Common B6401Table4NonK B6401Table4K B6401ListAndMCA
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation (priority := high) "X" => Polynomial.X
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

/-! ### Part 0: Small Kernel Checks & Numeric Helpers -/

lemma dXBi_zero {F : Type*} [CommRing F] : dXBi (0 : BiPoly F) = 0 := by
  apply Polynomial.ext; intro j; simp [coeff_dXBi]

lemma wdegBi_ge_natDegree_mul {F : Type*} [Field F] (wY : ℕ) (f : BiPoly F) (hf : f ≠ 0) :
    f.natDegree * wY ≤ wdegBi wY f := by
  have hj : f.natDegree ∈ f.support := Polynomial.mem_support_iff.mpr (by
    rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hf)
  exact (Nat.le_add_left _ _).trans
    (Finset.le_sup (f := fun j => (f.coeff j).natDegree + j * wY) hj)

lemma wdegBiDom_ge_natDegree_mul {A : Type*} [CommRing A] (wY : ℕ) (f : BiPoly A) (hf : f ≠ 0) :
    f.natDegree * wY ≤ wdegBiDom wY f := by
  have hj : f.natDegree ∈ f.support := Polynomial.mem_support_iff.mpr (by
    rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hf)
  exact (Nat.le_add_left _ _).trans
    (Finset.le_sup (f := fun j => (f.coeff j).natDegree + j * wY) hj)

lemma wdegBiDom_coeff_le_of_wdeg {A : Type*} [CommRing A] [IsDomain A] {wY W : ℕ} {Fpoly : ContactPoly A}
    (hW : wdeg wY Fpoly ≤ W) (k : ℕ) (hne : Fpoly.coeff k ≠ 0) :
    wdegBiDom wY (Fpoly.coeff k) + k * (wY - 1) ≤ W := by
  have hsupp : (Fpoly.coeff k).support.Nonempty := Polynomial.support_nonempty.mpr hne
  have hle : wdegBiDom wY (Fpoly.coeff k) ≤ W - k * (wY - 1) := by
    rw [wdegBiDom_le_iff]; intro j i hnz
    have := (wdeg_le_iff wY W Fpoly).mp hW k j i hnz; omega
  have hkw : k * (wY - 1) ≤ W := by
    obtain ⟨j, hj⟩ := hsupp
    have hne_j : (Fpoly.coeff k).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    have := (wdeg_le_iff wY W Fpoly).mp hW k j _ (Polynomial.leadingCoeff_ne_zero.mpr hne_j)
    omega
  omega

lemma wdegBiDom_le_of_wdeg_coeff {A : Type*} [CommRing A] [IsDomain A] {wY W : ℕ} {Fpoly : ContactPoly A}
    (hW : wdeg wY Fpoly ≤ W) (k : ℕ) :
    wdegBiDom wY (Fpoly.coeff k) ≤ W - k * (wY - 1) := by
  rw [wdegBiDom_le_iff]; intro j i hnz
  have := (wdeg_le_iff wY W Fpoly).mp hW k j i hnz; omega

theorem certsT1_no_p64 :
    certsT1.all (fun c => !c.cap1.useP64 && !c.cap2.useP64) = true := by decide

lemma checkCapWitness_d2_no_p64 {m s cHiNum cHiDen δNum δDen hiGNum hiGDen q₀ : ℕ} {w : CapWitness}
    (h : checkCapWitness 2 m s cHiNum cHiDen δNum δDen hiGNum hiGDen q₀ w = true) :
    w.useP64 = false := by
  cases hu : w.useP64
  · rfl
  · exfalso
    unfold checkCapWitness at h
    by_cases hbad : (m == 0 || s < 2 || cHiDen == 0 || δNum == 0 || δDen == 0 || hiGDen == 0) = true
    · simp only [hbad, ↓reduceIte] at h; cases h
    · simp only [hbad, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
      have hs := h.1
      unfold checkSideP64 at hs
      simp at hs

lemma evalContact_contactDeriv {F : Type*} [Field F] [CharP F 2]
    (Q : ContactPoly F) (P : Polynomial F) :
    evalContact (contactDeriv Q) P = (evalContact Q P).derivative := by
  have h2P : ∀ f : Polynomial F, f + f = 0 := CharTwo.add_self_eq_zero
  have hddP : P.derivative.derivative = 0 := by
    ext n
    rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative, Polynomial.coeff_zero]
    have hmul : ((n : F) + 1) * ((n : F) + 1 + 1) = 0 := by
      have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
      by_cases hev : n % 2 = 0
      · have : ((n + 2 : ℕ) : F) = 0 := by
          have hdiv : n + 2 = 2 * ((n + 2) / 2) := by omega
          calc ((n + 2 : ℕ) : F) = ((2 * ((n + 2) / 2) : ℕ) : F) := congrArg Nat.cast hdiv
            _ = (2 : F) * (((n + 2) / 2 : ℕ) : F) := by push_cast; rfl
            _ = 0 := by rw [h2F, zero_mul]
        have hrew : (n : F) + 1 + 1 = ((n + 2 : ℕ) : F) := by push_cast; ring
        rw [hrew, this, mul_zero]
      · have : ((n + 1 : ℕ) : F) = 0 := by
          have hdiv : n + 1 = 2 * ((n + 1) / 2) := by omega
          calc ((n + 1 : ℕ) : F) = ((2 * ((n + 1) / 2) : ℕ) : F) := congrArg Nat.cast hdiv
            _ = (2 : F) * (((n + 1) / 2 : ℕ) : F) := by push_cast; rfl
            _ = 0 := by rw [h2F, zero_mul]
        have hrew : (n : F) + 1 = ((n + 1 : ℕ) : F) := by push_cast; ring
        rw [hrew, this, zero_mul]
    calc P.coeff (n + 1 + 1) * (((n + 1 : ℕ) : F) + 1) * ((n : F) + 1)
        = P.coeff (n + 1 + 1) * (((n : F) + 1) * ((n : F) + 1 + 1)) := by push_cast; ring
      _ = 0 := by rw [hmul, mul_zero]
  have hbi : ∀ g : BiPoly F, (dXBi g).eval P + P.derivative * g.derivative.eval P = (g.eval P).derivative := by
    intro g
    induction g using Polynomial.induction_on' with
    | add a b ha hb =>
        rw [dXBi_add, Polynomial.derivative_add, Polynomial.eval_add, Polynomial.eval_add,
          Polynomial.eval_add, Polynomial.derivative_add, ← ha, ← hb]
        ring
    | monomial j p =>
        have hdX : dXBi (Polynomial.monomial j p) = Polynomial.monomial j p.derivative := by
          apply Polynomial.ext; intro m
          rw [coeff_dXBi, Polynomial.coeff_monomial, Polynomial.coeff_monomial]
          simp only [Finsupp.single_apply]; split_ifs <;> simp
        rw [hdX, Polynomial.derivative_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial,
          Polynomial.eval_monomial, Polynomial.derivative_mul, Polynomial.derivative_pow]
        cases j with
        | zero => simp
        | succ j' =>
            simp only [Nat.succ_sub_one, nsmul_eq_mul, Nat.cast_succ, map_add, map_one, map_natCast]
            ring
  induction Q using Polynomial.induction_on' with
  | add A B hA hB =>
      rw [contactDeriv_add, evalContact_add, evalContact_add, Polynomial.derivative_add, hA, hB]
  | monomial k g =>
      have hcd : contactDeriv (Polynomial.monomial k g) =
          Polynomial.monomial k (dXBi g) + Polynomial.monomial (k + 1) g.derivative := by
        apply Polynomial.ext; intro m
        rw [coeff_contactDeriv, Polynomial.coeff_add]
        simp only [Polynomial.coeff_monomial, Finsupp.single_apply]
        cases m with
        | zero => simp only [↓reduceIte, add_zero, Nat.succ_ne_zero]; split_ifs <;> simp [dXBi_zero]
        | succ m' =>
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, Nat.succ.injEq]
            split_ifs <;> simp [dXBi_zero]
      have hev_mon : ∀ (m : ℕ) (h : BiPoly F),
          evalContact (Polynomial.monomial m h) P = h.eval P * P.derivative ^ m := fun m h => by
        unfold evalContact
        rw [Polynomial.map_monomial, Polynomial.eval_monomial, Polynomial.coe_evalRingHom]
      rw [hcd, evalContact_add, hev_mon, hev_mon, hev_mon, Polynomial.derivative_mul,
        Polynomial.derivative_pow, hddP, mul_zero, mul_zero, add_zero, ← hbi g]
      rw [pow_succ]; ring

lemma card_le_of_biPoly_pow_1_bound (D_ZF : ℕ) :
    max ((2 * D_ZF : ℕ) : ℚ) (arklibBoundPowQ 1 1 (2 * D_ZF)) ≤
      (15000000 : ℚ) * (D_ZF : ℚ) + 2000000 := by
  have hDZ : (0 : ℚ) ≤ (D_ZF : ℚ) := Nat.cast_nonneg D_ZF
  apply max_le
  · push_cast; linarith
  · unfold arklibBoundPowQ
    norm_num [N, wY, A]
    linarith

lemma card_le_of_biPoly_pow_2_bound {D_ZF : ℕ} (hDZ : D_ZF ≤ 3850) :
    max ((2 * D_ZF : ℕ) : ℚ) (arklibBoundPowQ 2 1 (2 * D_ZF)) ≤ (80000000000 : ℚ) := by
  have hDZQ : (D_ZF : ℚ) ≤ 3850 := by exact_mod_cast hDZ
  apply max_le
  · push_cast; linarith
  · unfold arklibBoundPowQ
    norm_num [N, wY, A]
    linarith

lemma card_le_of_biPoly_pow_deg2_bound {B D_ZF : ℕ} (hB : B ≤ 24) (hDZ : D_ZF ≤ 3850) :
    max (D_ZF : ℚ) (arklibBoundPowQ 1 B D_ZF) ≤ (4000000000000 : ℚ) := by
  have hBQ : (B : ℚ) ≤ 24 := by exact_mod_cast hB
  have hB0 : (0 : ℚ) ≤ (B : ℚ) := Nat.cast_nonneg B
  have hDZQ : (D_ZF : ℚ) ≤ 3850 := by exact_mod_cast hDZ
  have hDZ0 : (0 : ℚ) ≤ (D_ZF : ℚ) := Nat.cast_nonneg D_ZF
  apply max_le
  · linarith
  · unfold arklibBoundPowQ
    have hsub0 : B - (2 * wY + 1) = 0 := by norm_num [wY]; omega
    rw [hsub0, Nat.cast_zero]
    have hmul : (B : ℚ) * (D_ZF : ℚ) ≤ 24 * 3850 :=
      mul_le_mul hBQ hDZQ hDZ0 (by norm_num)
    norm_num [N, wY, A]
    ring_nf at hmul ⊢
    linarith [hmul, hBQ, hDZ0]

/-! ### Part 1: Table 4 Row Transport & Single-Point Surplus Extraction -/

/-- Transport `baseT4Rows` validity & satisfaction from `(cLo1, cHi1, loG1, hiG1)` to
`(cLo2, cHi2, loG2, hiG2)` whenever `x ic ∈ [cLo2, cHi2]` and either the `G`-bucket is unchanged
or the target bucket is `SINGLE = (0, 1, 1, 1)`! -/
lemma baseT4Rows_transport {nv ic : ℕ} (hic_lt : ic < nv) (x : Fin nv → ℚ)
    {cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1 : ℕ}
    {cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2 : ℕ}
    (hcLoD2 : 0 < cLoD2) (hcHiD2 : 0 < cHiD2)
    (hcLo2 : (cLo2 : ℚ) / (cLoD2 : ℚ) ≤ x ⟨ic, hic_lt⟩)
    (hcHi2 : x ⟨ic, hic_lt⟩ ≤ (cHi2 : ℚ) / (cHiD2 : ℚ))
    (hG_case : (loG2 = loG1 ∧ loGD2 = loGD1 ∧ hiG2 = hiG1 ∧ hiGD2 = hiGD1) ∨
               (loG2 = 0 ∧ loGD2 = 1 ∧ hiG2 = 1 ∧ hiGD2 = 1))
    (hub_old : ∀ r ∈ (baseT4Rows ic cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).1,
      RowValid nv r ∧ RowSatLe x r)
    (heq_old : ∀ r ∈ (baseT4Rows ic cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).2,
      RowValid nv r ∧ RowSatEq x r) :
    (∀ r ∈ (baseT4Rows ic cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2).1,
      RowValid nv r ∧ RowSatLe x r) ∧
    (∀ r ∈ (baseT4Rows ic cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2).2,
      RowValid nv r ∧ RowSatEq x r) := by
  have hBpos : (0 : ℚ) < (BASE_DEN : ℚ) := by exact_mod_cast base_den_pos
  constructor
  · intro r hr
    unfold baseT4Rows at hr
    dsimp only at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hmem_old : ∀ row : SparseRow,
        row ∈ (baseT4Rows ic cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).1 →
        RowValid nv row ∧ RowSatLe x row := hub_old
    rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hr) | hr
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · refine ⟨⟨by dsimp; exact_mod_cast hcLoD2, by intro e he; simp at he; rcases he with rfl; exact hic_lt⟩, ?_⟩
      unfold RowSatLe
      simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hic_lt, ↓reduceDIte]
      rw [show (cI (-1) : ℚ) = -(BASE_DEN : ℚ) by unfold cI; push_cast; ring]
      push_cast
      have hmul := mul_le_mul_of_nonneg_left hcLo2 hBpos.le
      linarith [show (BASE_DEN : ℚ) * -(cLo2 : ℚ) / (cLoD2 : ℚ) = -((BASE_DEN : ℚ) * ((cLo2 : ℚ) / (cLoD2 : ℚ))) by ring]
    · refine ⟨⟨by dsimp; exact_mod_cast hcHiD2, by intro e he; simp at he; rcases he with rfl; exact hic_lt⟩, ?_⟩
      unfold RowSatLe
      simp only [evalRow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hic_lt, ↓reduceDIte]
      rw [show (cI 1 : ℚ) = (BASE_DEN : ℚ) by unfold cI; push_cast; ring]
      push_cast
      have hmul := mul_le_mul_of_nonneg_left hcHi2 hBpos.le
      linarith [show (BASE_DEN : ℚ) * (cHi2 : ℚ) / (cHiD2 : ℚ) = (BASE_DEN : ℚ) * ((cHi2 : ℚ) / (cHiD2 : ℚ)) by ring]
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · exact hmem_old _ (by unfold baseT4Rows; simp)
    · rcases hG_case with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact hmem_old _ (by unfold baseT4Rows; simp [hr])
      · simp at hr
    · rcases hG_case with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact hmem_old _ (by unfold baseT4Rows; simp [hr])
      · simp at hr
  · intro r hr
    exact heq_old r (by unfold baseT4Rows at hr ⊢; simpa using hr)

lemma buildT4ARows_transport (br : T4ABranch) (x : Fin (t4aNumVars br) → ℚ)
    {cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1 : ℕ}
    {cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2 : ℕ}
    (hcLoD2 : 0 < cLoD2) (hcHiD2 : 0 < cHiD2)
    (hcLo2 : (cLo2 : ℚ) / (cLoD2 : ℚ) ≤ x ⟨t4aNumVars br - 1, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩)
    (hcHi2 : x ⟨t4aNumVars br - 1, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ ≤ (cHi2 : ℚ) / (cHiD2 : ℚ))
    (hG_case : (loG2 = loG1 ∧ loGD2 = loGD1 ∧ hiG2 = hiG1 ∧ hiGD2 = hiGD1) ∨
               (loG2 = 0 ∧ loGD2 = 1 ∧ hiG2 = 1 ∧ hiGD2 = 1))
    (hub_old : ∀ r ∈ (buildT4ARows br cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).1.toList,
      RowValid (t4aNumVars br) r ∧ RowSatLe x r)
    (heq_old : ∀ r ∈ (buildT4ARows br cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).2.toList,
      RowValid (t4aNumVars br) r ∧ RowSatEq x r) :
    (∀ r ∈ (buildT4ARows br cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2).1.toList,
      RowValid (t4aNumVars br) r ∧ RowSatLe x r) ∧
    (∀ r ∈ (buildT4ARows br cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2).2.toList,
      RowValid (t4aNumVars br) r ∧ RowSatEq x r) := by
  have htr := baseT4Rows_transport (nv := t4aNumVars br) (ic := t4aNumVars br - 1)
    (by cases br <;> dsimp only [t4aNumVars] <;> omega) x hcLoD2 hcHiD2 hcLo2 hcHi2 hG_case
    (fun r hr => hub_old r (by simp only [buildT4ARows, List.toList_toArray, List.mem_append]; exact Or.inl hr))
    (fun r hr => heq_old r (by simp only [buildT4ARows, List.toList_toArray, List.mem_append]; exact Or.inl hr))
  constructor
  · intro r hr
    simp only [buildT4ARows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact htr.1 r hr
    · exact hub_old r (by simp only [buildT4ARows, List.toList_toArray, List.mem_append]; exact Or.inr hr)
  · intro r hr
    simp only [buildT4ARows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact htr.2 r hr
    · exact heq_old r (by simp only [buildT4ARows, List.toList_toArray, List.mem_append]; exact Or.inr hr)

lemma buildT4BRows_transport (br : T4BBranch) (x : Fin 49 → ℚ)
    {cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1 : ℕ}
    {cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2 : ℕ}
    (hcLoD2 : 0 < cLoD2) (hcHiD2 : 0 < cHiD2)
    (hcLo2 : (cLo2 : ℚ) / (cLoD2 : ℚ) ≤ x ⟨48, by decide⟩)
    (hcHi2 : x ⟨48, by decide⟩ ≤ (cHi2 : ℚ) / (cHiD2 : ℚ))
    (hG_case : (loG2 = loG1 ∧ loGD2 = loGD1 ∧ hiG2 = hiG1 ∧ hiGD2 = hiGD1) ∨
               (loG2 = 0 ∧ loGD2 = 1 ∧ hiG2 = 1 ∧ hiGD2 = 1))
    (hub_old : ∀ r ∈ (buildT4BRows br cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).1.toList,
      RowValid 49 r ∧ RowSatLe x r)
    (heq_old : ∀ r ∈ (buildT4BRows br cLo1 cLoD1 cHi1 cHiD1 loG1 loGD1 hiG1 hiGD1).2.toList,
      RowValid 49 r ∧ RowSatEq x r) :
    (∀ r ∈ (buildT4BRows br cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2).1.toList,
      RowValid 49 r ∧ RowSatLe x r) ∧
    (∀ r ∈ (buildT4BRows br cLo2 cLoD2 cHi2 cHiD2 loG2 loGD2 hiG2 hiGD2).2.toList,
      RowValid 49 r ∧ RowSatEq x r) := by
  have htr := baseT4Rows_transport (nv := 49) (ic := 48)
    (by decide) x hcLoD2 hcHiD2 hcLo2 hcHi2 hG_case
    (fun r hr => hub_old r (by simp only [buildT4BRows, List.toList_toArray, List.mem_append]; exact Or.inl hr))
    (fun r hr => heq_old r (by simp only [buildT4BRows, List.toList_toArray, List.mem_append]; exact Or.inl hr))
  constructor
  · intro r hr
    simp only [buildT4BRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact htr.1 r hr
    · exact hub_old r (by simp only [buildT4BRows, List.toList_toArray, List.mem_append]; exact Or.inr hr)
  · intro r hr
    simp only [buildT4BRows, List.toList_toArray, List.mem_append] at hr
    rcases hr with hr | hr
    · exact htr.2 r hr
    · exact heq_old r (by simp only [buildT4BRows, List.toList_toArray, List.mem_append]; exact Or.inr hr)

/-- Concavity linearization: `(∑ i, rankDiffQ 1 m s (D.k i)) / N ≤ ∑_{j < 4} rankDiffQ(j) x_j + (rd3 - rd2) x_4`. -/
lemma sum_rankDiffQ_le_linearized (D : KerD45Data) {nv : ℕ} (h5 : 5 < nv) (m s : ℕ) (hm : 0 < m)
    (x : Fin nv → ℚ)
    (hx0 : x ⟨0, by omega⟩ = (D.n0 : ℚ) / (N : ℚ))
    (hx1 : x ⟨1, by omega⟩ = (D.n1 : ℚ) / (N : ℚ))
    (hx2 : x ⟨2, by omega⟩ = (D.n2 : ℚ) / (N : ℚ))
    (hx3 : x ⟨3, by omega⟩ = (D.n3 : ℚ) / (N : ℚ))
    (hx4 : x ⟨4, by omega⟩ = (D.nt : ℚ) / (N : ℚ)) :
    (∑ i : Idx, rankDiffQ 1 m s (D.k i)) / (N : ℚ) ≤
      (∑ j : Fin 4, rankDiffQ 1 m s j.val * x ⟨j.val, by omega⟩) +
      (rankDiffQ 1 m s 3 - rankDiffQ 1 m s 2) * x ⟨4, by omega⟩ := by
  have hNpos : (0 : ℚ) < (N : ℚ) := by norm_num [N]
  have hm2pos : (0 : ℚ) < (m : ℚ) * (m : ℚ) := by
    have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
    positivity
  have hpt : ∀ i : Idx,
      rankDiffQ 1 m s (D.k i) ≤
        (if D.k i = 0 then rankDiffQ 1 m s 0 else 0) +
        (if D.k i = 1 then rankDiffQ 1 m s 1 else 0) +
        (if D.k i = 2 then rankDiffQ 1 m s 2 else 0) +
        (if 3 ≤ D.k i then rankDiffQ 1 m s 3 else 0) +
        (rankDiffQ 1 m s 3 - rankDiffQ 1 m s 2) * ((D.k i - 3 : ℕ) : ℚ) := by
    intro i
    by_cases h0 : D.k i = 0
    · simp [h0]
    by_cases h1 : D.k i = 1
    · simp [h1]
    by_cases h2 : D.k i = 2
    · simp [h2]
    have h3 : 3 ≤ D.k i := by omega
    simp only [h0, h1, h2, h3, ↓reduceIte, zero_add, add_zero]
    unfold rankDiffQ
    have hnat := rankKerD_diff_le_linear_tail m s 1 3 (D.k i) (by omega) h3
    have hle23 : rankKerD m s - rankKerD (m - 2) (s - 1) ≤ rankKerD m s - rankKerD (m - 3) (s - 1) := by
      have hmono : rankKerD (m - 3) (s - 1) ≤ rankKerD (m - 2) (s - 1) :=
        rankKerD_mono_left (s - 1) (by omega)
      omega
    have hQ : ((rankKerD m s - rankKerD (m - D.k i) (s - 1) : ℕ) : ℚ) ≤
        ((rankKerD m s - rankKerD (m - 3) (s - 1) : ℕ) : ℚ) +
        (((rankKerD m s - rankKerD (m - 3) (s - 1) : ℕ) : ℚ) -
         ((rankKerD m s - rankKerD (m - 2) (s - 1) : ℕ) : ℚ)) * ((D.k i - 3 : ℕ) : ℚ) := by
      have hcast : ((rankKerD m s - rankKerD (m - D.k i) (s - 1) : ℕ) : ℚ) ≤
          (((rankKerD m s - rankKerD (m - 3) (s - 1)) +
            (D.k i - 3) * ((rankKerD m s - rankKerD (m - 3) (s - 1)) -
              (rankKerD m s - rankKerD (m - 2) (s - 1))) : ℕ) : ℚ) := by
        exact_mod_cast hnat
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hle23] at hcast
      linarith
    have hdiv := div_le_div_of_nonneg_right hQ hm2pos.le
    calc _ ≤ _ := hdiv
      _ = _ := by ring
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  have hrhs_eq :
      (∑ i : Idx, ((if D.k i = 0 then rankDiffQ 1 m s 0 else 0) +
        (if D.k i = 1 then rankDiffQ 1 m s 1 else 0) +
        (if D.k i = 2 then rankDiffQ 1 m s 2 else 0) +
        (if 3 ≤ D.k i then rankDiffQ 1 m s 3 else 0) +
        (rankDiffQ 1 m s 3 - rankDiffQ 1 m s 2) * ((D.k i - 3 : ℕ) : ℚ))) / (N : ℚ) =
      (∑ j : Fin 4, rankDiffQ 1 m s j.val * x ⟨j.val, by omega⟩) +
      (rankDiffQ 1 m s 3 - rankDiffQ 1 m s 2) * x ⟨4, by omega⟩ := by
    have hgen : ∀ S0 : Finset Idx,
        (∑ i ∈ S0, ((if D.k i = 0 then rankDiffQ 1 m s 0 else 0) +
          (if D.k i = 1 then rankDiffQ 1 m s 1 else 0) +
          (if D.k i = 2 then rankDiffQ 1 m s 2 else 0) +
          (if 3 ≤ D.k i then rankDiffQ 1 m s 3 else 0) +
          (rankDiffQ 1 m s 3 - rankDiffQ 1 m s 2) * ((D.k i - 3 : ℕ) : ℚ))) =
        ((S0.filter fun i => D.k i = 0).card : ℚ) * rankDiffQ 1 m s 0 +
        ((S0.filter fun i => D.k i = 1).card : ℚ) * rankDiffQ 1 m s 1 +
        ((S0.filter fun i => D.k i = 2).card : ℚ) * rankDiffQ 1 m s 2 +
        ((S0.filter fun i => 3 ≤ D.k i).card : ℚ) * rankDiffQ 1 m s 3 +
        (rankDiffQ 1 m s 3 - rankDiffQ 1 m s 2) * (∑ i ∈ S0, ((D.k i - 3 : ℕ) : ℚ)) := by
      intro S0
      simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [hgen Finset.univ]
    have hnt_cast : (∑ i : Idx, ((D.k i - 3 : ℕ) : ℚ)) = (D.nt : ℚ) := by
      unfold KerD45Data.nt; rw [Nat.cast_sum]
    rw [hnt_cast]
    have hfc : ∀ {P : Idx → Prop} (i1 i2 : DecidablePred P),
        (@Finset.filter Idx P i1 Finset.univ).card = (@Finset.filter Idx P i2 Finset.univ).card :=
      fun _ _ => congrArg Finset.card (by ext i; simp only [Finset.mem_filter])
    have hn0 : (Finset.univ.filter fun i : Idx => D.k i = 0).card = D.n0 := by
      unfold KerD45Data.n0; exact hfc _ _
    have hn1 : (Finset.univ.filter fun i : Idx => D.k i = 1).card = D.n1 := by
      unfold KerD45Data.n1; exact hfc _ _
    have hn2 : (Finset.univ.filter fun i : Idx => D.k i = 2).card = D.n2 := by
      unfold KerD45Data.n2; exact hfc _ _
    have hn3 : (Finset.univ.filter fun i : Idx => 3 ≤ D.k i).card = D.n3 := by
      unfold KerD45Data.n3; exact hfc _ _
    rw [hn0, hn1, hn2, hn3]
    simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two,
      show (3 : Fin 4).val = 3 from rfl, hx0, hx1, hx2, hx3, hx4]
    ring
  rw [← hrhs_eq]
  exact div_le_div_of_nonneg_right hsum hNpos.le

/-- Extract strict quotient surplus + `CapWitness` checks from a satisfied `checkT4Bucket = true`. -/
lemma table4_surplus_from_bucket (D : KerD45Data) {nv : ℕ} (h5 : 5 < nv)
    (rows : Array SparseRow × Array SparseRow)
    (cLoNum cLoDen cHiNum cHiDen : ℕ) (b : T4BucketCert)
    (hchk : checkT4Bucket nv rows.1 rows.2 cLoNum cLoDen cHiNum cHiDen b = true)
    (hcLo : (cLoNum : ℚ) / (cLoDen : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ))
    (hcHi : (D.W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (x : Fin nv → ℚ) (hx_nn : ∀ j, 0 ≤ x j)
    (hx0 : x ⟨0, by omega⟩ = (D.n0 : ℚ) / (N : ℚ))
    (hx1 : x ⟨1, by omega⟩ = (D.n1 : ℚ) / (N : ℚ))
    (hx2 : x ⟨2, by omega⟩ = (D.n2 : ℚ) / (N : ℚ))
    (hx3 : x ⟨3, by omega⟩ = (D.n3 : ℚ) / (N : ℚ))
    (hx4 : x ⟨4, by omega⟩ = (D.nt : ℚ) / (N : ℚ))
    (hxic : x ⟨nv - 1, by omega⟩ = (D.W_F : ℚ) / (wY : ℚ))
    (hub : ∀ r ∈ rows.1.toList, RowValid nv r ∧ RowSatLe x r)
    (heq : ∀ r ∈ rows.2.toList, RowValid nv r ∧ RowSatEq x r) :
    0 < b.m ∧ 1 ≤ b.s ∧ 0 < cHiDen ∧ 0 < b.δNum ∧ 0 < b.δDen ∧ 0 < b.hiGDen ∧
    (b.δNum : ℚ) / (b.δDen : ℚ) <
      vquotLbQ 1 b.m b.s ((D.W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 1 b.m b.s (D.k i)) / (N : ℚ) ∧
    checkCapWitness 1 b.m b.s cHiNum cHiDen b.δNum b.δDen b.hiGNum b.hiGDen 1 b.cap1 = true ∧
    checkCapWitness 1 b.m b.s cHiNum cHiDen b.δNum b.δDen b.hiGNum b.hiGDen 2 b.cap2 = true := by
  have hmem1 : ∀ i (hi : i < rows.1.size), rows.1[i] ∈ rows.1.toList := fun i hi =>
    Array.mem_toList_iff.mpr (Array.getElem_mem hi)
  have hmem2 : ∀ i (hi : i < rows.2.size), rows.2[i] ∈ rows.2.toList := fun i hi =>
    Array.mem_toList_iff.mpr (Array.getElem_mem hi)
  have ⟨hm0, hm_pos_fn⟩ := checkT4Bucket_sound rows.1 rows.2 cLoNum cLoDen cHiNum cHiDen b hchk
    (fun i hi => (hub _ (hmem1 i hi)).1.1)
    (fun i hi => (heq _ (hmem2 i hi)).1.1)
    (fun i hi => (hub _ (hmem1 i hi)).1.2)
    (fun i hi => (heq _ (hmem2 i hi)).1.2)
    x hx_nn
    (fun i hi => (hub _ (hmem1 i hi)).2)
    (fun i hi => (heq _ (hmem2 i hi)).2)
  have hmpos : 0 < b.m := Nat.pos_of_ne_zero hm0
  obtain ⟨h5', hfn⟩ := hm_pos_fn hmpos
  have ⟨hsurp_lin, hcap1, hcap2⟩ := hfn (by rw [hxic]; exact hcLo) (by rw [hxic]; exact hcHi)
  have hlin_le := sum_rankDiffQ_le_linearized D h5' b.m b.s hmpos x hx0 hx1 hx2 hx3 hx4
  have hsurp : (b.δNum : ℚ) / (b.δDen : ℚ) <
      vquotLbQ 1 b.m b.s ((D.W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 1 b.m b.s (D.k i)) / (N : ℚ) := by
    rw [hxic] at hsurp_lin; linarith
  have hpars : 1 ≤ b.s ∧ 0 < cHiDen ∧ 0 < b.δNum ∧ 0 < b.δDen ∧ 0 < b.hiGDen := by
    unfold checkCapWitness at hcap1
    by_contra hbad
    have hif : (b.m == 0 || b.s < 1 || cHiDen == 0 || b.δNum == 0 || b.δDen == 0 || b.hiGDen == 0) = true := by
      push Not at hbad
      rcases lt_or_ge b.s 1 with hs | hs
      · simp [hs]
      · rcases Nat.eq_zero_or_pos cHiDen with hc | hc
        · simp [hc]
        · rcases Nat.eq_zero_or_pos b.δNum with hd1 | hd1
          · simp [hd1]
          · rcases Nat.eq_zero_or_pos b.δDen with hd2 | hd2
            · simp [hd2]
            · have h0 : b.hiGDen = 0 := by have := hbad hs hc hd1 hd2; omega
              simp [h0]
    rw [if_pos hif] at hcap1; cases hcap1
  exact ⟨hmpos, hpars.1, hpars.2.1, hpars.2.2.1, hpars.2.2.2.1, hpars.2.2.2.2, hsurp, hcap1, hcap2⟩

/-- Bundled single-point Table 4 surplus witness (either `SINGLE` with `useP64 = false` or `STD5` at slot `r`). -/
def T4SingleWitness (W_F : ℕ) (k : Idx → ℕ) : Prop :=
  ∃ (m s cHiNum cHiDen δNum δDen : ℕ) (w1 w2 : CapWitness),
    0 < m ∧ m ≤ 3000 ∧ 1 ≤ s ∧ s ≤ 300 ∧ 0 < cHiDen ∧ 0 < δNum ∧ 0 < δDen ∧
    (W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ) ∧
    (δNum : ℚ) / (δDen : ℚ) <
      vquotLbQ 1 m s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 1 m s (k i)) / (N : ℚ) ∧
    checkCapWitness 1 m s cHiNum cHiDen δNum δDen 1 1 1 w1 = true ∧
    checkCapWitness 1 m s cHiNum cHiDen δNum δDen 1 1 2 w2 = true ∧
    w1.useP64 = false ∧ w2.useP64 = false ∧
    w1.c1Bkt ≤ SINGLE_C1 ∧ w1.c0Bkt ≤ SINGLE_C0 ∧
    w2.c1Bkt * 3850 + w2.c0Bkt ≤ SINGLE_Q2

def T4Std5Witness (W_F : ℕ) (k : Idx → ℕ) (r : Fin 5) : Prop :=
  let bd := std5Bounds r
  ∃ (m s cHiNum cHiDen δNum δDen : ℕ) (w1 w2 : CapWitness),
    0 < m ∧ m ≤ 3000 ∧ 1 ≤ s ∧ s ≤ 300 ∧ 0 < cHiDen ∧ 0 < δNum ∧ 0 < δDen ∧ 0 < bd.2.2.2 ∧
    (W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ) ∧
    (δNum : ℚ) / (δDen : ℚ) <
      vquotLbQ 1 m s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 1 m s (k i)) / (N : ℚ) ∧
    checkCapWitness 1 m s cHiNum cHiDen δNum δDen bd.2.2.1 bd.2.2.2 1 w1 = true ∧
    checkCapWitness 1 m s cHiNum cHiDen δNum δDen bd.2.2.1 bd.2.2.2 2 w2 = true ∧
    (bd.2.2.1 = bd.2.2.2 → w1.useP64 = false ∧ w2.useP64 = false) ∧
    w1.c1Bkt ≤ std5C1 r ∧ w1.c0Bkt ≤ std5C0 r ∧
    w2.c1Bkt * 3850 + w2.c0Bkt ≤ std5Q2 r

lemma t4_start_end_bounds (D : KerD45Data) (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5) :
    0 < T4_START_D ∧ 0 < T4_END_D ∧ T4_START_N * T4_END_D < T4_END_N * T4_START_D ∧
    (T4_START_N : ℚ) / (T4_START_D : ℚ) ≤ (D.W_F : ℚ) / (wY : ℚ) ∧
    (D.W_F : ℚ) / (wY : ℚ) ≤ (T4_END_N : ℚ) / (T4_END_D : ℚ) := by
  refine ⟨by norm_num [T4_START_D, wY], by norm_num [T4_END_D],
          by norm_num [T4_START_N, T4_START_D, T4_END_N, T4_END_D, wY], ?_, ?_⟩
  · unfold T4_START_N T4_START_D
    have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
    apply div_le_div_of_nonneg_right _ hwQ.le
    have h1 : 5 * wY - 1 ≤ D.W_F := by have := D.hWF_lo; omega
    exact_mod_cast h1
  · simpa [T4_END_N, T4_END_D] using hWF_hi

private lemma checkT4GridBin_cases_mem {nv : Nat}
    {rowBuilder : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Array SparseRow × Array SparseRow}
    {bin : T4BinCert} (h : checkT4GridBin nv rowBuilder bin = true) :
    (∃ b ∈ bin.buckets,
      b.loGNum = 0 ∧ b.loGDen = 1 ∧ b.hiGNum = 1 ∧ b.hiGDen = 1 ∧
      (let rows := rowBuilder bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen 0 1 1 1
       checkT4Bucket nv rows.1 rows.2 bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen b = true) ∧
      (b.m = 0 ∨ (b.cap1.c1Bkt ≤ SINGLE_C1 ∧ b.cap1.c0Bkt ≤ SINGLE_C0 ∧
        b.cap2.c1Bkt * 3850 + b.cap2.c0Bkt ≤ SINGLE_Q2))) ∨
    (∀ r : Fin 5, ∃ b ∈ bin.buckets,
      let bd := std5Bounds r
      b.loGNum = bd.1 ∧ b.loGDen = bd.2.1 ∧ b.hiGNum = bd.2.2.1 ∧ b.hiGDen = bd.2.2.2 ∧
      (let rows := rowBuilder bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen bd.1 bd.2.1 bd.2.2.1 bd.2.2.2
       checkT4Bucket nv rows.1 rows.2 bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen b = true) ∧
      (b.m = 0 ∨ (b.cap1.c1Bkt ≤ std5C1 r ∧ b.cap1.c0Bkt ≤ std5C0 r ∧
        b.cap2.c1Bkt * 3850 + b.cap2.c0Bkt ≤ std5Q2 r))) := by
  unfold checkT4GridBin at h
  rcases hbk : bin.buckets with _ | ⟨b0, r0⟩
  · simp [hbk] at h
  · rcases r0 with _ | ⟨b1, r1⟩
    · simp only [hbk] at h
      exact Or.inl ⟨b0, by simp [hbk], checkGridBucket_spec h⟩
    · rcases r1 with _ | ⟨b2, r2⟩
      · simp [hbk] at h
      · rcases r2 with _ | ⟨b3, r3⟩
        · simp [hbk] at h
        · rcases r3 with _ | ⟨b4, r4⟩
          · simp [hbk] at h
          · rcases r4 with _ | ⟨b5, r5⟩
            · simp only [hbk, Bool.and_eq_true] at h
              rcases h with ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
              right; intro r
              fin_cases r
              · exact ⟨b0, by simp [hbk], checkGridBucket_spec h0⟩
              · exact ⟨b1, by simp [hbk], checkGridBucket_spec h1⟩
              · exact ⟨b2, by simp [hbk], checkGridBucket_spec h2⟩
              · exact ⟨b3, by simp [hbk], checkGridBucket_spec h3⟩
              · exact ⟨b4, by simp [hbk], checkGridBucket_spec h4⟩
            · simp [hbk] at h

/-- Turn a `T4ABranch` satisfaction witness at `(T4_START, T4_END, std5Bounds r)` into
`T4SingleWitness ∨ T4Std5Witness r`. -/
lemma t4_witness_of_t4a (D : KerD45Data) (r : Fin 5) (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5)
    (br : T4ABranch)
    (hvalid : match br with
      | .det | .p0Zero => True
      | .p0 m21Nz _ p0M10D4 q2M21M10 => m21Nz = false → p0M10D4 = true ∧ q2M21M10 = false
      | .b1c1 _ _ bCase => bCase < 6)
    (x : Fin (t4aNumVars br) → ℚ) (hx_nn : ∀ j, 0 ≤ x j)
    (hx0 : x ⟨0, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n0 : ℚ) / (N : ℚ))
    (hx1 : x ⟨1, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n1 : ℚ) / (N : ℚ))
    (hx2 : x ⟨2, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n2 : ℚ) / (N : ℚ))
    (hx3 : x ⟨3, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.n3 : ℚ) / (N : ℚ))
    (hx4 : x ⟨4, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.nt : ℚ) / (N : ℚ))
    (hxic : x ⟨t4aNumVars br - 1, by cases br <;> dsimp only [t4aNumVars] <;> omega⟩ = (D.W_F : ℚ) / (wY : ℚ))
    (hub : ∀ row ∈ (buildT4ARows br T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2).1.toList,
      RowValid (t4aNumVars br) row ∧ RowSatLe x row)
    (heq : ∀ row ∈ (buildT4ARows br T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2).2.toList,
      RowValid (t4aNumVars br) row ∧ RowSatEq x row) :
    T4SingleWitness D.W_F D.k ∨ T4Std5Witness D.W_F D.k r := by
  have ⟨hsD, heD, hslt, hlo, hhi⟩ := t4_start_end_bounds D hWF_hi
  obtain ⟨bin, hbin_mem, hloD, hhiD, hbin_lo, hbin_hi, hbin_ok⟩ :=
    exists_bin_of_checkT4GridBranch hsD heD hslt (t4aBins_ok br hvalid) ((D.W_F : ℚ) / (wY : ℚ)) hlo hhi
  have hms_bin := List.all_eq_true.mp (t4a_ms_bound br hvalid) bin hbin_mem
  have hnop64_bin := List.all_eq_true.mp (t4a_hi1_no_p64 br hvalid) bin hbin_mem
  have h5 : 5 < t4aNumVars br := by cases br <;> dsimp only [t4aNumVars] <;> omega
  rcases checkT4GridBin_cases_mem hbin_ok with ⟨b, hb_mem, hloN, hloD', hhiN, hhiD', hb_chk, hb_cap⟩ | hstd5
  · left
    have htr := buildT4ARows_transport br x hloD hhiD (by rw [hxic]; exact hbin_lo) (by rw [hxic]; exact hbin_hi)
      (Or.inr ⟨rfl, rfl, rfl, rfl⟩) hub heq
    have ⟨hm, hs, hcHiD, hδN, hδD, _, hsurp, hc1, hc2⟩ :=
      table4_surplus_from_bucket D h5 _ bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen b hb_chk
        hbin_lo hbin_hi x hx_nn hx0 hx1 hx2 hx3 hx4 hxic htr.1 htr.2
    have hms_b := List.all_eq_true.mp hms_bin b hb_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hms_b
    have hnop64 := no_p64_of_binNoP64AtHi1 hnop64_bin hb_mem (by omega)
    have hcaps := hb_cap.resolve_left hm.ne'
    rw [hhiN, hhiD'] at hc1 hc2
    exact ⟨b.m, b.s, bin.cHiNum, bin.cHiDen, b.δNum, b.δDen, b.cap1, b.cap2,
      hm, hms_b.1, hs, hms_b.2, hcHiD, hδN, hδD, hbin_hi, hsurp, hc1, hc2,
      hnop64.1, hnop64.2, hcaps.1, hcaps.2.1, hcaps.2.2⟩
  · right
    obtain ⟨b, hb_mem, hloN, hloD', hhiN, hhiD', hb_chk, hb_cap⟩ := hstd5 r
    have htr := buildT4ARows_transport br x hloD hhiD (by rw [hxic]; exact hbin_lo) (by rw [hxic]; exact hbin_hi)
      (Or.inl ⟨rfl, rfl, rfl, rfl⟩) hub heq
    have ⟨hm, hs, hcHiD, hδN, hδD, hhiGD, hsurp, hc1, hc2⟩ :=
      table4_surplus_from_bucket D h5 _ bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen b hb_chk
        hbin_lo hbin_hi x hx_nn hx0 hx1 hx2 hx3 hx4 hxic htr.1 htr.2
    have hms_b := List.all_eq_true.mp hms_bin b hb_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hms_b
    have hcaps := hb_cap.resolve_left hm.ne'
    rw [hhiN, hhiD'] at hc1 hc2
    rw [hhiD'] at hhiGD
    refine ⟨b.m, b.s, bin.cHiNum, bin.cHiDen, b.δNum, b.δDen, b.cap1, b.cap2,
      hm, hms_b.1, hs, hms_b.2, hcHiD, hδN, hδD, hhiGD, hbin_hi, hsurp, hc1, hc2,
      fun heq1 => no_p64_of_binNoP64AtHi1 hnop64_bin hb_mem (by omega),
      hcaps.1, hcaps.2.1, hcaps.2.2⟩

/-- Turn a `T4BBranch` satisfaction witness at `(T4_START, T4_END, std5Bounds r)` into
`T4SingleWitness ∨ T4Std5Witness r`. -/
lemma t4_witness_of_t4b (D : KerD45Data) (r : Fin 5) (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5)
    (br : T4BBranch) (hq1 : br.q1Case < 3) (hode : br.odeCase < 7)
    (x : Fin 49 → ℚ) (hx_nn : ∀ j, 0 ≤ x j)
    (hx0 : x ⟨0, by decide⟩ = (D.n0 : ℚ) / (N : ℚ))
    (hx1 : x ⟨1, by decide⟩ = (D.n1 : ℚ) / (N : ℚ))
    (hx2 : x ⟨2, by decide⟩ = (D.n2 : ℚ) / (N : ℚ))
    (hx3 : x ⟨3, by decide⟩ = (D.n3 : ℚ) / (N : ℚ))
    (hx4 : x ⟨4, by decide⟩ = (D.nt : ℚ) / (N : ℚ))
    (hxic : x ⟨48, by decide⟩ = (D.W_F : ℚ) / (wY : ℚ))
    (hub : ∀ row ∈ (buildT4BRows br T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2).1.toList,
      RowValid 49 row ∧ RowSatLe x row)
    (heq : ∀ row ∈ (buildT4BRows br T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2).2.toList,
      RowValid 49 row ∧ RowSatEq x row) :
    T4SingleWitness D.W_F D.k ∨ T4Std5Witness D.W_F D.k r := by
  have ⟨hsD, heD, hslt, hlo, hhi⟩ := t4_start_end_bounds D hWF_hi
  have hbins : ∃ bins : List T4BinCert,
      checkT4GridBranch 49 (buildT4BRows br) T4_START_N T4_START_D T4_END_N T4_END_D bins = true ∧
      bins.all binMsBound = true ∧ bins.all binNoP64AtHi1 = true := by
    cases hr : br.rGt
    · exact ⟨t4b1Bins br, t4b1Bins_ok br hr hq1 hode, t4b1_ms_bound br hr hq1 hode, t4b1_hi1_no_p64 br hr hq1 hode⟩
    · exact ⟨t4b2Bins br, t4b2Bins_ok br hr hq1 hode, t4b2_ms_bound br hr hq1 hode, t4b2_hi1_no_p64 br hr hq1 hode⟩
  obtain ⟨bins, hbins_ok, hbins_ms, hbins_p64⟩ := hbins
  obtain ⟨bin, hbin_mem, hloD, hhiD, hbin_lo, hbin_hi, hbin_ok⟩ :=
    exists_bin_of_checkT4GridBranch hsD heD hslt hbins_ok ((D.W_F : ℚ) / (wY : ℚ)) hlo hhi
  have hms_bin := List.all_eq_true.mp hbins_ms bin hbin_mem
  have hnop64_bin := List.all_eq_true.mp hbins_p64 bin hbin_mem
  rcases checkT4GridBin_cases_mem hbin_ok with ⟨b, hb_mem, hloN, hloD', hhiN, hhiD', hb_chk, hb_cap⟩ | hstd5
  · left
    have htr := buildT4BRows_transport br x hloD hhiD (by rw [hxic]; exact hbin_lo) (by rw [hxic]; exact hbin_hi)
      (Or.inr ⟨rfl, rfl, rfl, rfl⟩) hub heq
    have ⟨hm, hs, hcHiD, hδN, hδD, _, hsurp, hc1, hc2⟩ :=
      table4_surplus_from_bucket D (by omega : 5 < 49) _ bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen b hb_chk
        hbin_lo hbin_hi x hx_nn hx0 hx1 hx2 hx3 hx4 hxic htr.1 htr.2
    have hms_b := List.all_eq_true.mp hms_bin b hb_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hms_b
    have hnop64 := no_p64_of_binNoP64AtHi1 hnop64_bin hb_mem (by omega)
    have hcaps := hb_cap.resolve_left hm.ne'
    rw [hhiN, hhiD'] at hc1 hc2
    exact ⟨b.m, b.s, bin.cHiNum, bin.cHiDen, b.δNum, b.δDen, b.cap1, b.cap2,
      hm, hms_b.1, hs, hms_b.2, hcHiD, hδN, hδD, hbin_hi, hsurp, hc1, hc2,
      hnop64.1, hnop64.2, hcaps.1, hcaps.2.1, hcaps.2.2⟩
  · right
    obtain ⟨b, hb_mem, hloN, hloD', hhiN, hhiD', hb_chk, hb_cap⟩ := hstd5 r
    have htr := buildT4BRows_transport br x hloD hhiD (by rw [hxic]; exact hbin_lo) (by rw [hxic]; exact hbin_hi)
      (Or.inl ⟨rfl, rfl, rfl, rfl⟩) hub heq
    have ⟨hm, hs, hcHiD, hδN, hδD, hhiGD, hsurp, hc1, hc2⟩ :=
      table4_surplus_from_bucket D (by omega : 5 < 49) _ bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen b hb_chk
        hbin_lo hbin_hi x hx_nn hx0 hx1 hx2 hx3 hx4 hxic htr.1 htr.2
    have hms_b := List.all_eq_true.mp hms_bin b hb_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hms_b
    have hcaps := hb_cap.resolve_left hm.ne'
    rw [hhiN, hhiD'] at hc1 hc2
    rw [hhiD'] at hhiGD
    refine ⟨b.m, b.s, bin.cHiNum, bin.cHiDen, b.δNum, b.δDen, b.cap1, b.cap2,
      hm, hms_b.1, hs, hms_b.2, hcHiD, hδN, hδD, hhiGD, hbin_hi, hsurp, hc1, hc2,
      fun heq1 => no_p64_of_binNoP64AtHi1 hnop64_bin hb_mem (by omega),
      hcaps.1, hcaps.2.1, hcaps.2.2⟩

/-- Table 4 exact integer gap `G_z = W_F - (wY - 1) - (a1 + 3 a2 + 5 a3) + a0`. -/
def G_val (W_F : ℕ) (k : Idx → ℕ) (Az : Finset Idx) : ℤ :=
  (W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
    (((Az.filter fun i => k i = 1).card + 3 * (Az.filter fun i => k i = 2).card +
      5 * (Az.filter fun i => 3 ≤ k i).card : ℕ) : ℤ) +
    ((Az.filter fun i => k i = 0).card : ℤ)

lemma G_val_eq_D (D : KerD45Data) :
    G_val D.W_F D.k D.Az = (D.W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
      ((D.a1 + 3 * D.a2 + 5 * D.a3 : ℕ) : ℤ) + (D.a0 : ℤ) := by
  have hfc : ∀ {P : Idx → Prop} (i1 i2 : DecidablePred P),
      (@Finset.filter Idx P i1 D.Az).card = (@Finset.filter Idx P i2 D.Az).card :=
    fun _ _ => congrArg Finset.card (by ext i; simp only [Finset.mem_filter])
  have ha0 : (D.Az.filter fun i => D.k i = 0).card = D.a0 := by unfold KerD45Data.a0; exact hfc _ _
  have ha1 : (D.Az.filter fun i => D.k i = 1).card = D.a1 := by unfold KerD45Data.a1; exact hfc _ _
  have ha2 : (D.Az.filter fun i => D.k i = 2).card = D.a2 := by unfold KerD45Data.a2; exact hfc _ _
  have ha3 : (D.Az.filter fun i => 3 ≤ D.k i).card = D.a3 := by unfold KerD45Data.a3; exact hfc _ _
  unfold G_val
  rw [ha0, ha1, ha2, ha3]

lemma G_val_nonneg (D : KerD45Data) : 0 ≤ G_val D.W_F D.k D.Az := by
  rw [G_val_eq_D]
  have h1 := D.a1_3a2_5a3_le
  have h2 := D.hWF_lo
  have hw : 1 ≤ wY := by norm_num [wY]
  omega

lemma sum_2k_sub_1_le_G_val (W_F : ℕ) (k : Idx → ℕ) (Az : Finset Idx) :
    (W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) - ∑ i ∈ Az, (2 * (k i : ℤ) - 1) ≤ G_val W_F k Az := by
  unfold G_val
  have hsum :
      (((Az.filter fun i => k i = 1).card + 3 * (Az.filter fun i => k i = 2).card +
        5 * (Az.filter fun i => 3 ≤ k i).card : ℕ) : ℤ) -
      ((Az.filter fun i => k i = 0).card : ℤ) ≤ ∑ i ∈ Az, (2 * (k i : ℤ) - 1) := by
    have hrew :
        (((Az.filter fun i => k i = 1).card + 3 * (Az.filter fun i => k i = 2).card +
          5 * (Az.filter fun i => 3 ≤ k i).card : ℕ) : ℤ) -
        ((Az.filter fun i => k i = 0).card : ℤ) =
        ∑ i ∈ Az, ((if k i = 1 then (1 : ℤ) else 0) + (if k i = 2 then 3 else 0) +
          (if 3 ≤ k i then 5 else 0) - (if k i = 0 then 1 else 0)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite,
        Finset.sum_const_zero, add_zero, sub_zero, Finset.sum_const, nsmul_eq_mul]
      push_cast; ring
    rw [hrew]
    apply Finset.sum_le_sum; intro i _; split_ifs <;> omega
  omega

/-- Universal `STD5` bucket slot selector for `G ≥ 0`. -/
def std5Slot (G : ℤ) : Fin 5 :=
  if 100 * G ≤ (N : ℤ) then 0
  else if 100 * G ≤ 3 * (N : ℤ) then 1
  else if 50 * G ≤ 3 * (N : ℤ) then 2
  else if 10 * G ≤ (N : ℤ) then 3
  else 4

lemma std5Slot_spec {G : ℤ} (hG : 0 ≤ G) :
    let r := std5Slot G
    let bd := std5Bounds r
    0 < bd.2.1 ∧ 0 < bd.2.2.2 ∧
    (bd.2.1 : ℤ) * G ≥ (bd.1 * N : ℤ) ∧
    (bd.2.2.1 < bd.2.2.2 → (bd.2.2.2 : ℤ) * G ≤ (bd.2.2.1 * N : ℤ)) := by
  unfold std5Slot
  split_ifs with h0 h1 h2 h3
  · dsimp [std5Bounds]; refine ⟨by decide, by decide, by omega, fun _ => by omega⟩
  · dsimp [std5Bounds]; refine ⟨by decide, by decide, by omega, fun _ => by omega⟩
  · dsimp [std5Bounds]; refine ⟨by decide, by decide, by omega, fun _ => by omega⟩
  · dsimp [std5Bounds]; refine ⟨by decide, by decide, by omega, fun _ => by omega⟩
  · dsimp [std5Bounds]; refine ⟨by decide, by decide, by omega, fun h => by omega⟩

lemma t4_point_det_witness (D : KerD45Data) (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5)
    (hdet : D.detM ≠ 0) :
    T4SingleWitness D.W_F D.k ∨ T4Std5Witness D.W_F D.k (std5Slot (G_val D.W_F D.k D.Az)) := by
  set r := std5Slot (G_val D.W_F D.k D.Az) with hr_def
  have ⟨hsD, heD, _, hlo, hhi⟩ := t4_start_end_bounds D hWF_hi
  have ⟨hloGD, hhiGD, hloG, hhiG⟩ := std5Slot_spec (G_val_nonneg D)
  rw [← hr_def] at hloGD hhiGD hloG hhiG
  rw [G_val_eq_D] at hloG hhiG
  obtain ⟨x, hxnn, hx0, hx1, hx2, hx3, hx4, hxic, hub, heq⟩ :=
    D.table4_det_sat hdet T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2
      hsD heD hloGD hhiGD hlo hhi hloG hhiG
  exact t4_witness_of_t4a D r hWF_hi .det trivial x hxnn hx0 hx1 hx2 hx3 hx4 hxic hub heq

lemma t4_point_p0Zero_witness (D : KerD45Data) (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5)
    (hminors : ∀ j : Fin 3, D.Bj 2 * D.Cj j + D.Cj 2 * D.Bj j = 0) :
    T4SingleWitness D.W_F D.k ∨ T4Std5Witness D.W_F D.k (std5Slot (G_val D.W_F D.k D.Az)) := by
  have h2ne : D.Bj 2 ≠ 0 ∨ D.Cj 2 ≠ 0 := by
    by_contra hall; push Not at hall
    apply D.g2_ne_zero
    unfold KerD45Data.gj; rw [hall.1, hall.2, Polynomial.zero_comp, mul_zero, add_zero]
  let g := EuclideanDomain.gcd (D.Bj 2) (D.Cj 2)
  have hg_ne : g ≠ 0 := by
    intro h0; have := EuclideanDomain.gcd_eq_zero_iff.mp h0
    rcases h2ne with h | h <;> exact h (by tauto)
  rcases EuclideanDomain.gcd_dvd_left (D.Bj 2) (D.Cj 2) with ⟨c, hc⟩
  rcases EuclideanDomain.gcd_dvd_right (D.Bj 2) (D.Cj 2) with ⟨b, hb⟩
  have hcb_ne : c ≠ 0 ∨ b ≠ 0 := by
    rcases h2ne with h | h
    · left; intro hc0; rw [hc0, mul_zero] at hc; exact h hc
    · right; intro hb0; rw [hb0, mul_zero] at hb; exact h hb
  have hcop : ∀ d : Polynomial Fld, d ∣ c → d ∣ b → IsUnit d := by
    intro d hdc hdb
    have hd1 : g * d ∣ D.Bj 2 := by rw [hc]; exact mul_dvd_mul_left g hdc
    have hd2 : g * d ∣ D.Cj 2 := by rw [hb]; exact mul_dvd_mul_left g hdb
    have hd : g * d ∣ g := EuclideanDomain.dvd_gcd hd1 hd2
    rcases hd with ⟨u, hu⟩
    exact isUnit_iff_exists_inv.mpr ⟨u, mul_left_cancel₀ hg_ne (by
      calc g * (d * u) = g * d * u := by ring
        _ = g := hu.symm
        _ = g * 1 := (mul_one g).symm)⟩
  have hsyz : ∀ j : Fin 3, c * D.Cj j + b * D.Bj j = 0 := by
    intro j; apply mul_left_cancel₀ hg_ne; rw [mul_zero]
    calc g * (c * D.Cj j + b * D.Bj j) = (g * c) * D.Cj j + (g * b) * D.Bj j := by ring
      _ = D.Bj 2 * D.Cj j + D.Cj 2 * D.Bj j := by rw [← hc, ← hb]
      _ = 0 := hminors j
  set r := std5Slot (G_val D.W_F D.k D.Az) with hr_def
  have ⟨hsD, heD, _, hlo, hhi⟩ := t4_start_end_bounds D hWF_hi
  have ⟨hloGD, hhiGD, hloG, hhiG⟩ := std5Slot_spec (G_val_nonneg D)
  rw [← hr_def] at hloGD hhiGD hloG hhiG
  rw [G_val_eq_D] at hloG hhiG
  obtain ⟨x, hxnn, hx0, hx1, hx2, hx3, hx4, hxic, hub, heq⟩ :=
    D.table4_p0Zero_sat hcb_ne hcop hsyz T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2
      hsD heD hloGD hhiGD hlo hhi hloG hhiG
  exact t4_witness_of_t4a D r hWF_hi .p0Zero trivial x hxnn hx0 hx1 hx2 hx3 hx4 hxic hub heq

lemma t4_point_syzygy_witness {D : KerD45Data} (S : KerD45Syzygy D)
    (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5) :
    T4SingleWitness D.W_F D.k ∨ T4Std5Witness D.W_F D.k (std5Slot (G_val D.W_F D.k D.Az)) := by
  set r := std5Slot (G_val D.W_F D.k D.Az) with hr_def
  have ⟨hsD, heD, _, hlo, hhi⟩ := t4_start_end_bounds D hWF_hi
  have ⟨hloGD, hhiGD, hloG, hhiG⟩ := std5Slot_spec (G_val_nonneg D)
  rw [← hr_def] at hloGD hhiGD hloG hhiG
  rw [G_val_eq_D] at hloG hhiG
  rcases table4_algebra_of_syzygy S T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2
      hsD heD hloGD hhiGD hlo hhi hloG hhiG with
    ⟨br, hvalid, x, hxnn, hx0, hx1, hx2, hx3, hx4, hxic, hub, heq⟩ |
    ⟨br, hq1, hode, x, hxnn, hx0, hx1, hx2, hx3, hx4, hxic, hub, heq⟩
  · exact t4_witness_of_t4a D r hWF_hi br hvalid x hxnn hx0 hx1 hx2 hx3 hx4 hxic hub heq
  · exact t4_witness_of_t4b D r hWF_hi br hq1 hode x hxnn hx0 hx1 hx2 hx3 hx4 hxic hub heq

lemma t4_point_dichotomy (D : KerD45Data) (hWF_hi : (D.W_F : ℚ) / (wY : ℚ) ≤ 28 / 5) :
    EscapeUZero D ∨ T4SingleWitness D.W_F D.k ∨ T4Std5Witness D.W_F D.k (std5Slot (G_val D.W_F D.k D.Az)) := by
  set r := std5Slot (G_val D.W_F D.k D.Az) with hr_def
  have ⟨hsD, heD, _, hlo, hhi⟩ := t4_start_end_bounds D hWF_hi
  have ⟨hloGD, hhiGD, hloG, hhiG⟩ := std5Slot_spec (G_val_nonneg D)
  rw [← hr_def] at hloGD hhiGD hloG hhiG
  rw [G_val_eq_D] at hloG hhiG
  rcases table4_algebra_dichotomy D T4_START_N T4_START_D T4_END_N T4_END_D
      (std5Bounds r).1 (std5Bounds r).2.1 (std5Bounds r).2.2.1 (std5Bounds r).2.2.2
      hsD heD hloGD hhiGD hlo hhi hloG hhiG with
    hesc |
    ⟨br, hvalid, x, hxnn, hx0, hx1, hx2, hx3, hx4, hxic, hub, heq⟩ |
    ⟨br, hq1, hode, x, hxnn, hx0, hx1, hx2, hx3, hx4, hxic, hub, heq⟩
  · exact Or.inl hesc
  · exact Or.inr (t4_witness_of_t4a D r hWF_hi br hvalid x hxnn hx0 hx1 hx2 hx3 hx4 hxic hub heq)
  · exact Or.inr (t4_witness_of_t4b D r hWF_hi br hq1 hode x hxnn hx0 hx1 hx2 hx3 hx4 hxic hub heq)

/-! ### Part 2: Global `Z`-Specialization & Table 4 Syzygy Helpers -/

lemma card_evalZ_poly_eq_zero_le (P : Polynomial (Polynomial Fld)) {H : ℕ}
    (hP : P ≠ 0) (hH : ∀ a, (P.coeff a).natDegree ≤ H) (S : Finset Fld) :
    (S.filter fun z => P.map (Polynomial.evalRingHom z) = 0).card ≤ H := by
  classical
  have hex : ∃ a, P.coeff a ≠ 0 := by
    by_contra hall; push Not at hall; apply hP; apply Polynomial.ext; intro a; exact hall a
  obtain ⟨a, ha⟩ := hex
  let q := P.coeff a
  have hsub : (S.filter fun z => P.map (Polynomial.evalRingHom z) = 0) ⊆ q.roots.toFinset := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots ha, Polynomial.IsRoot.def]
    have h0 := congrArg (fun r : Polynomial Fld => r.coeff a) hz.2
    simpa [q] using h0
  calc (S.filter fun z => P.map (Polynomial.evalRingHom z) = 0).card
      ≤ q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ q.roots.card := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := Polynomial.card_roots' q
    _ ≤ H := hH a

lemma card_evalZBiPoly_good_deg_le (G : BiPoly (Polynomial Fld)) {H : ℕ}
    (hG : G ≠ 0) (hH : ∀ j a, ((G.coeff j).coeff a).natDegree ≤ H) (S : Finset Fld) :
    (S.filter fun z => ¬ (evalZBiPoly G z ≠ 0 ∧ (evalZBiPoly G z).natDegree = G.natDegree)).card ≤ H := by
  classical
  have hlc : G.coeff G.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hG
  have hsub : (S.filter fun z => ¬ (evalZBiPoly G z ≠ 0 ∧ (evalZBiPoly G z).natDegree = G.natDegree)) ⊆
      S.filter fun z => (G.coeff G.natDegree).map (Polynomial.evalRingHom z) = 0 := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    refine ⟨hz.1, ?_⟩
    by_contra hnz
    apply hz.2
    have hcoeff : (evalZBiPoly G z).coeff G.natDegree ≠ 0 := by simpa [evalZBiPoly] using hnz
    refine ⟨fun h0 => hcoeff (by simp [h0]), le_antisymm Polynomial.natDegree_map_le (Polynomial.le_natDegree_of_ne_zero hcoeff)⟩
  exact (Finset.card_le_card hsub).trans (card_evalZ_poly_eq_zero_le _ hlc (fun a => hH G.natDegree a) S)

lemma card_evalZBiPoly_natDegree_lt_le (G : BiPoly (Polynomial Fld)) {H : ℕ}
    (hG : G ≠ 0) (hH : ∀ j a, ((G.coeff j).coeff a).natDegree ≤ H) (S : Finset Fld) :
    (S.filter fun z => (evalZBiPoly G z).natDegree ≠ G.natDegree).card ≤ H := by
  classical
  refine (Finset.card_le_card fun z hz => ?_).trans (card_evalZBiPoly_good_deg_le G hG hH S)
  rw [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, fun h => hz.2 h.2⟩

lemma degZ_mul_poly_le {A B : Polynomial (Polynomial Fld)} {DA DB : ℕ}
    (hA : ∀ a, (A.coeff a).natDegree ≤ DA) (hB : ∀ a, (B.coeff a).natDegree ≤ DB) (a : ℕ) :
    ((A * B).coeff a).natDegree ≤ DA + DB := by
  rw [Polynomial.coeff_mul]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun x _ => ?_)
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hA x.1) (hB x.2))

lemma degZ_prod_poly_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial Fld)) (D : ℕ)
    (hf : ∀ i ∈ s, ∀ a, ((f i).coeff a).natDegree ≤ D) (a : ℕ) :
    ((∏ i ∈ s, f i).coeff a).natDegree ≤ s.card * D := by
  classical
  induction s using Finset.induction_on generalizing a with
  | empty =>
      simp only [Finset.prod_empty, Polynomial.coeff_one, Finset.card_empty, zero_mul]
      split_ifs <;> simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.add_one_mul]
      have h1 := degZ_mul_poly_le (hf i (Finset.mem_insert_self i s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)) a
      omega

lemma degZ_resultant_biPoly_le (f g : BiPoly (Polynomial Fld)) (df dg D : ℕ)
    (hf : ∀ j a, ((f.coeff j).coeff a).natDegree ≤ D)
    (hg : ∀ j a, ((g.coeff j).coeff a).natDegree ≤ D) (a : ℕ) :
    ((Polynomial.resultant f g df dg).coeff a).natDegree ≤ (df + dg) * D :=
  B6401PointSurplus.degZ_resultant_biPoly_le f g df dg D hf hg a

lemma resultant_54_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {f0 f1 : Polynomial R} (hd0 : f0.natDegree ≤ 5) (hd1 : f1.natDegree = 4)
    (hf1 : f1 ≠ 0) (hres : Polynomial.resultant f0 f1 f0.natDegree 4 ≠ 0) :
    Polynomial.resultant f0 f1 5 4 ≠ 0 := by
  have h5 : f0.natDegree + (5 - f0.natDegree) = 5 := Nat.add_sub_of_le hd0
  rw [← h5, Polynomial.resultant_add_left_deg f0 f1 f0.natDegree 4 (5 - f0.natDegree) le_rfl]
  have hlc : f1.coeff 4 ≠ 0 := by rw [← hd1, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hf1
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hlc)) hres
  have : ((-1 : R) ^ (4 * (5 - f0.natDegree))) = 1 := by
    rw [pow_mul]; norm_num
  rw [this]; exact one_ne_zero

/-- Global `T`-polynomials `(P_j^Z, C_j^Z, B_j^Z)` in `Fld[Z][T]` for a Table 4 factor. -/
noncomputable def PjZ {W_F : ℕ} (f_coord : KerDIdx wY W_F 1 → Polynomial Fld) (j : Fin 3) :
    Polynomial (Polynomial Fld) :=
  ∑ e : KerDIdx wY W_F 1,
    if e.1.1 = 0 ∧ e.1.2.1 = 0 ∧ e.1.2.2.1 = j.val then Polynomial.monomial e.1.2.2.2 (f_coord e) else 0

noncomputable def CjZ {W_F : ℕ} (f_coord : KerDIdx wY W_F 1 → Polynomial Fld) (j : Fin 3) :
    Polynomial (Polynomial Fld) :=
  ∑ e : KerDIdx wY W_F 1,
    if e.1.1 = 1 ∧ e.1.2.1 = 0 ∧ e.1.2.2.1 = j.val then Polynomial.monomial e.1.2.2.2 (f_coord e) else 0

noncomputable def BjZ {W_F : ℕ} (f_coord : KerDIdx wY W_F 1 → Polynomial Fld) (j : Fin 3) :
    Polynomial (Polynomial Fld) :=
  ∑ e : KerDIdx wY W_F 1,
    if e.1.1 = 0 ∧ e.1.2.1 = 1 ∧ e.1.2.2.1 = j.val then Polynomial.monomial e.1.2.2.2 (f_coord e) else 0

lemma map_PjZ {W_F : ℕ} (f_coord : KerDIdx wY W_F 1 → Polynomial Fld) (j : Fin 3) (z : Fld)
    (D : KerD45Data) (hWF : D.W_F = W_F)
    (hfc : ∀ e : KerDIdx wY W_F 1, (f_coord e).eval z = D.f_coord ⟨e.1, hWF ▸ e.2⟩) :
    (PjZ f_coord j).map (Polynomial.evalRingHom z) = D.Pj j := by
  subst hWF
  unfold PjZ KerD45Data.Pj
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl; intro e _
  split_ifs
  · rw [Polynomial.map_monomial, Polynomial.coe_evalRingHom, hfc e]
  · rw [Polynomial.map_zero]

lemma map_CjZ {W_F : ℕ} (f_coord : KerDIdx wY W_F 1 → Polynomial Fld) (j : Fin 3) (z : Fld)
    (D : KerD45Data) (hWF : D.W_F = W_F)
    (hfc : ∀ e : KerDIdx wY W_F 1, (f_coord e).eval z = D.f_coord ⟨e.1, hWF ▸ e.2⟩) :
    (CjZ f_coord j).map (Polynomial.evalRingHom z) = D.Cj j := by
  subst hWF
  unfold CjZ KerD45Data.Cj
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl; intro e _
  split_ifs
  · rw [Polynomial.map_monomial, Polynomial.coe_evalRingHom, hfc e]
  · rw [Polynomial.map_zero]

lemma map_BjZ {W_F : ℕ} (f_coord : KerDIdx wY W_F 1 → Polynomial Fld) (j : Fin 3) (z : Fld)
    (D : KerD45Data) (hWF : D.W_F = W_F)
    (hfc : ∀ e : KerDIdx wY W_F 1, (f_coord e).eval z = D.f_coord ⟨e.1, hWF ▸ e.2⟩) :
    (BjZ f_coord j).map (Polynomial.evalRingHom z) = D.Bj j := by
  subst hWF
  unfold BjZ KerD45Data.Bj
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl; intro e _
  split_ifs
  · rw [Polynomial.map_monomial, Polynomial.coe_evalRingHom, hfc e]
  · rw [Polynomial.map_zero]

lemma degZ_PjZ_le {W_F D_ZF : ℕ} (f_coord : KerDIdx wY W_F 1 → Polynomial Fld)
    (hfc : ∀ e, (f_coord e).natDegree ≤ D_ZF) (j : Fin 3) (a : ℕ) :
    ((PjZ f_coord j).coeff a).natDegree ≤ D_ZF := by
  unfold PjZ; rw [finset_sum_coeff]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => ?_)
  dsimp only [Function.comp_apply]
  split_ifs
  · simp only [Polynomial.coeff_monomial, Finsupp.single_apply]; split_ifs <;> simp [hfc e]
  · simp

lemma degZ_CjZ_le {W_F D_ZF : ℕ} (f_coord : KerDIdx wY W_F 1 → Polynomial Fld)
    (hfc : ∀ e, (f_coord e).natDegree ≤ D_ZF) (j : Fin 3) (a : ℕ) :
    ((CjZ f_coord j).coeff a).natDegree ≤ D_ZF := by
  unfold CjZ; rw [finset_sum_coeff]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => ?_)
  dsimp only [Function.comp_apply]
  split_ifs
  · simp only [Polynomial.coeff_monomial, Finsupp.single_apply]; split_ifs <;> simp [hfc e]
  · simp

lemma degZ_BjZ_le {W_F D_ZF : ℕ} (f_coord : KerDIdx wY W_F 1 → Polynomial Fld)
    (hfc : ∀ e, (f_coord e).natDegree ≤ D_ZF) (j : Fin 3) (a : ℕ) :
    ((BjZ f_coord j).coeff a).natDegree ≤ D_ZF := by
  unfold BjZ; rw [finset_sum_coeff]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => ?_)
  dsimp only [Function.comp_apply]
  split_ifs
  · simp only [Polynomial.coeff_monomial, Finsupp.single_apply]; split_ifs <;> simp [hfc e]
  · simp

/-- Elementary `2 × 2` minor proportionality lemma in characteristic 2:
two kernel vectors of a `2 × 3` matrix whose `(1, 2)` minor is nonzero are proportional. -/
private lemma syzygy_prop_of_minor_ne_zero {R : Type*} [CommRing R] [IsDomain R] [CharP R 2]
    {P1 C1 B1 P2 C2 B2 p1 c1 b1 p2 c2 b2 : R}
    (h11 : p1 * P1 + c1 * C1 + b1 * B1 = 0) (h12 : p1 * P2 + c1 * C2 + b1 * B2 = 0)
    (h21 : p2 * P1 + c2 * C1 + b2 * B1 = 0) (h22 : p2 * P2 + c2 * C2 + b2 * B2 = 0)
    (hΔ : C1 * B2 + C2 * B1 ≠ 0) :
    p1 * c2 = p2 * c1 ∧ p1 * b2 = p2 * b1 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  have hc1 : c1 * (C1 * B2 + C2 * B1) = p1 * (P1 * B2 + P2 * B1) := by
    linear_combination B2 * h11 + B1 * h12 - (p1 * (P1 * B2 + P2 * B1) + b1 * B1 * B2) * h2
  have hc2 : c2 * (C1 * B2 + C2 * B1) = p2 * (P1 * B2 + P2 * B1) := by
    linear_combination B2 * h21 + B1 * h22 - (p2 * (P1 * B2 + P2 * B1) + b2 * B1 * B2) * h2
  have hb1 : b1 * (C1 * B2 + C2 * B1) = p1 * (P1 * C2 + P2 * C1) := by
    linear_combination C2 * h11 + C1 * h12 - (p1 * (P1 * C2 + P2 * C1) + c1 * C1 * C2) * h2
  have hb2 : b2 * (C1 * B2 + C2 * B1) = p2 * (P1 * C2 + P2 * C1) := by
    linear_combination C2 * h21 + C1 * h22 - (p2 * (P1 * C2 + P2 * C1) + c2 * C1 * C2) * h2
  constructor
  · apply mul_right_cancel₀ hΔ
    calc p1 * c2 * (C1 * B2 + C2 * B1) = p1 * (c2 * (C1 * B2 + C2 * B1)) := by ring
      _ = p1 * (p2 * (P1 * B2 + P2 * B1)) := by rw [hc2]
      _ = p2 * (p1 * (P1 * B2 + P2 * B1)) := by ring
      _ = p2 * (c1 * (C1 * B2 + C2 * B1)) := by rw [← hc1]
      _ = p2 * c1 * (C1 * B2 + C2 * B1) := by ring
  · apply mul_right_cancel₀ hΔ
    calc p1 * b2 * (C1 * B2 + C2 * B1) = p1 * (b2 * (C1 * B2 + C2 * B1)) := by ring
      _ = p1 * (p2 * (P1 * C2 + P2 * C1)) := by rw [hb2]
      _ = p2 * (p1 * (P1 * C2 + P2 * C1)) := by ring
      _ = p2 * (b1 * (C1 * B2 + C2 * B1)) := by rw [← hb1]
      _ = p2 * b1 * (C1 * B2 + C2 * B1) := by ring

/-- In char 2, if a `3 × 3` matrix has determinant `0`, then the cofactor vector of any two rows `(r1, r2)`
annihilates all 3 rows! -/
private lemma char2_det3_cofactor_syzygy {R : Type*} [CommRing R] [CharP R 2]
    (P0 P1 P2 C0 C1 C2 B0 B1 B2 : R)
    (hdet : P0 * C1 * B2 + C0 * B1 * P2 + B0 * P1 * C2 + P2 * C1 * B0 + C2 * B1 * P0 + B2 * P1 * C0 = 0) :
    let P : Fin 3 → R := ![P0, P1, P2]
    let C : Fin 3 → R := ![C0, C1, C2]
    let B : Fin 3 → R := ![B0, B1, B2]
    ∀ r1 r2 j : Fin 3,
      (C r1 * B r2 + C r2 * B r1) * P j +
      (P r1 * B r2 + P r2 * B r1) * C j +
      (P r1 * C r2 + P r2 * C r1) * B j = 0 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  intro P C B r1 r2 j
  by_cases h12 : r1 = r2
  · subst h12; simp only [CharTwo.add_self_eq_zero, zero_mul, add_zero]
  · by_cases hj1 : j = r1
    · rw [hj1]
      linear_combination (P r1 * C r1 * B r2 + P r1 * C r2 * B r1 + P r2 * C r1 * B r1) * h2
    · by_cases hj2 : j = r2
      · rw [hj2]
        linear_combination (P r2 * C r1 * B r2 + P r2 * C r2 * B r1 + P r1 * C r2 * B r2) * h2
      · fin_cases r1 <;> fin_cases r2 <;> fin_cases j <;>
          try (exfalso; first | exact h12 rfl | exact hj1 rfl | exact hj2 rfl)
        all_goals (dsimp [P, C, B]; linear_combination hdet)

private lemma char2_det3_eq_sum {R : Type*} [CommRing R] [CharP R 2] (M : Matrix (Fin 3) (Fin 3) R) :
    M.det =
      M 0 0 * M 1 1 * M 2 2 + M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 +
      M 2 0 * M 1 1 * M 0 2 + M 2 1 * M 1 2 * M 0 0 + M 2 2 * M 1 0 * M 0 1 := by
  rw [Matrix.det_fin_three]
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination -(M 0 0 * M 1 2 * M 2 1 + M 0 1 * M 1 0 * M 2 2 + M 0 2 * M 1 1 * M 2 0) * h2

/-- Convert `p(Z, T), c(Z, T), b(Z, T) ∈ Fld[Z][T]` into the linear-in-`Y` trivariate
`U_Z(Z, X, Y) = (b(Z, X^2) + X * c(Z, X^2)) + p(Z, X^2) * Y : BiPoly (Polynomial Fld)`! -/
noncomputable def makeEscapeUZ (pZ cZ bZ : Polynomial (Polynomial Fld)) : BiPoly (Polynomial Fld) :=
  Polynomial.C (bZ.comp (Polynomial.X ^ 2) + Polynomial.X * cZ.comp (Polynomial.X ^ 2)) +
  Polynomial.C (pZ.comp (Polynomial.X ^ 2)) * Polynomial.X

lemma makeEscapeUZ_ne_zero {pZ cZ bZ : Polynomial (Polynomial Fld)} (hp : pZ ≠ 0) :
    makeEscapeUZ pZ cZ bZ ≠ 0 := by
  intro h0
  have h1 := congrArg (fun q : BiPoly (Polynomial Fld) => q.coeff 1) h0
  simp only [makeEscapeUZ, Polynomial.coeff_add, Polynomial.coeff_C, one_ne_zero, ↓reduceIte,
    zero_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_zero] at h1
  apply hp; apply Polynomial.ext; intro a
  have ha := congrArg (fun q : Polynomial (Polynomial Fld) => q.coeff (2 * a)) h1
  rw [comp_X_sq_coeff_even, Polynomial.coeff_zero] at ha
  exact ha

lemma makeEscapeUZ_natDegree_le (pZ cZ bZ : Polynomial (Polynomial Fld)) :
    (makeEscapeUZ pZ cZ bZ).natDegree ≤ 1 := by
  unfold makeEscapeUZ
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (by rw [Polynomial.natDegree_C]; exact Nat.zero_le 1) ?_)
  exact (Polynomial.natDegree_mul_le).trans (by simp [Polynomial.natDegree_C, Polynomial.natDegree_X])

lemma makeEscapeUZ_degZ_le {pZ cZ bZ : Polynomial (Polynomial Fld)} {H : ℕ}
    (hp : ∀ a, (pZ.coeff a).natDegree ≤ H) (hc : ∀ a, (cZ.coeff a).natDegree ≤ H)
    (hb : ∀ a, (bZ.coeff a).natDegree ≤ H) (j a : ℕ) :
    (((makeEscapeUZ pZ cZ bZ).coeff j).coeff a).natDegree ≤ H := by
  unfold makeEscapeUZ
  have hcomp_deg : ∀ (q : Polynomial (Polynomial Fld)), (∀ t, (q.coeff t).natDegree ≤ H) →
      ∀ m, ((q.comp (Polynomial.X ^ 2)).coeff m).natDegree ≤ H := fun q hq m => by
    by_cases he : m % 2 = 0
    · rw [show m = 2 * (m / 2) by omega, comp_X_sq_coeff_even]; exact hq _
    · rw [show m = 2 * (m / 2) + 1 by omega, comp_X_sq_coeff_odd]; simp
  rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
  split_ifs with h0 h1
  · subst h0; omega
  · simp only [add_zero, Polynomial.coeff_add]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (hcomp_deg bZ hb a) ?_)
    cases a with
    | zero => rw [Polynomial.coeff_X_mul_zero]; simp
    | succ a' => rw [Polynomial.coeff_X_mul]; exact hcomp_deg cZ hc a'
  · simp only [zero_add]; exact hcomp_deg pZ hp a
  · simp

lemma triEval_makeEscapeUZ (pZ cZ bZ : Polynomial (Polynomial Fld)) (z : Fld) (P : Polynomial Fld) :
    triEval (makeEscapeUZ pZ cZ bZ) z P =
      (pZ.map (Polynomial.evalRingHom z)).comp (Polynomial.X ^ 2) * P +
      (bZ.map (Polynomial.evalRingHom z)).comp (Polynomial.X ^ 2) +
      Polynomial.X * (cZ.map (Polynomial.evalRingHom z)).comp (Polynomial.X ^ 2) := by
  unfold triEval makeEscapeUZ
  have hmap_comp : ∀ q : Polynomial (Polynomial Fld),
      (q.comp (Polynomial.X ^ 2)).map (Polynomial.evalRingHom z) =
        (q.map (Polynomial.evalRingHom z)).comp (Polynomial.X ^ 2) := fun q => by
    rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.coe_mapRingHom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, hmap_comp]
  ring

/-! ### Part 3: Unified Single-Factor Bounds (`deg1_factor_card_le` & `deg2_factor_card_le`) -/

/-- **Unified `deg_R = 1` Single-Factor Bound (Tables 1 & 4, `q₀ ∈ {1, 2}`):**
For ANY irreducible `ker(D)` factor `F ∈ K_{W_F}(1)[Z]` with `W_F / wY ≤ 51 / 2` and `wYZ q₀ F ≤ D_ZF`:
- If `q₀ = 1`: `(S.card : ℚ) ≤ (T4_C1_SUM + 15000060) * D_ZF + (T4_C0_SUM + 2000000)`.
- If `q₀ = 2` (with `W_F / wY < 13`, `D_ZF ≤ 3850`): `(S.card : ℚ) ≤ T4_Q2_SUM + 80000231000`. -/
theorem deg1_factor_card_le
    (u₀ u₁ : Idx → Fld) {W_F D_ZF q₀ : ℕ} (hq₀ : q₀ = 1 ∨ q₀ = 2)
    (hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2)
    (hq2_cond : q₀ = 2 → (W_F : ℚ) / (wY : ℚ) < 13 ∧ D_ZF ≤ 3850)
    (f_coord : KerDIdx wY W_F 1 → Polynomial Fld)
    (hirr : Irreducible (liftCRat (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1)))
    (hFdeg : (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1).natDegree = 1)
    (hFwdeg : wdeg wY (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) = W_F)
    (hf_wYZ : wYZ q₀ (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) ≤ D_ZF)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hFvan : ∀ z ∈ S, evalContact (evalZContact (∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1) z) (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6401 u₀ u₁ (Az z)) :
    (S.card : ℚ) ≤
      if q₀ = 1 then ((T4_C1_SUM + 15000060 : ℕ) : ℚ) * (D_ZF : ℚ) + ((T4_C0_SUM + 2000000 : ℕ) : ℚ)
      else ((T4_Q2_SUM + 80000231000 : ℕ) : ℚ) := by
  classical
  let Fpoly : ContactPoly (Polynomial Fld) := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
  have hFne : Fpoly ≠ 0 := fun h0 => hirr.ne_zero (by change liftCRat Fpoly = 0; rw [h0, map_zero])
  have hf1_ne : Fpoly.coeff 1 ≠ 0 := by
    rw [← hFdeg, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hFne
  have hWF_lo : 1 * (wY - 1) ≤ W_F := by
    have h1 := wdegBiDom_coeff_le_of_wdeg (le_of_eq hFwdeg) 1 hf1_ne; omega
  have hZ_F : ∀ k' j' i', (((Fpoly.coeff k').coeff j').coeff i').natDegree ≤ D_ZF :=
    natDegree_Z_le_of_wYZ hf_wYZ
  have hfc_deg : ∀ e : KerDIdx wY W_F 1, (f_coord e).natDegree ≤ D_ZF := by
    intro e
    by_cases he : f_coord e = 0
    · simp [he]
    · have h1 := coord_wYZ_le_of_wYZ_ne (by norm_num [wY]) f_coord hf_wYZ e he
      omega
  -- Global exact local orders `k i` (independent of `z`!)
  let Loc (i : Idx) : LocalPoly (Polynomial Fld) :=
    ∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (Polynomial.C (BinaryIRSProfile.domain i)) (linePow u₀ u₁ q₀ i) e.1
  have hLoc_ne : ∀ i : Idx, Loc i ≠ 0 := fun i =>
    localShift_ne_zero (Polynomial.C (BinaryIRSProfile.domain i)) (linePow u₀ u₁ q₀ i) f_coord hFne
  let k : Idx → ℕ := fun i => exactTwOrd (Loc i)
  have hk_exact : ∀ i : Idx, twOrdGE (Loc i) (k i) ∧ (∀ m, k i < m → ∃ p q, p + q = k i ∧ twCoeff (Loc i) p q ≠ 0) :=
    fun i => ⟨twOrdGE_exactTwOrd (hLoc_ne i), fun _ _ => exists_twCoeff_exactTwOrd (hLoc_ne i)⟩
  have hvan_z : ∀ (z : Fld) (i : Idx),
      twOrdGE (∑ e : KerDIdx wY W_F 1,
        locC ((f_coord e).eval z) * kerDLocalPoly (BinaryIRSProfile.domain i) (u₀ i + z ^ q₀ * u₁ i) e.1) (k i) := by
    intro z i
    have h1 := twOrdGE_evalZLocal_sum (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) f_coord z (hk_exact i).1
    simpa only [eval_linePow] using h1
  let f0 := Fpoly.coeff 0
  let f1 := Fpoly.coeff 1
  have hf0_degZ : ∀ j a, ((f0.coeff j).coeff a).natDegree ≤ D_ZF := fun j a => hZ_F 0 j a
  have hf1_degZ : ∀ j a, ((f1.coeff j).coeff a).natDegree ≤ D_ZF := fun j a => hZ_F 1 j a
  have hd0_le25 : f0.natDegree ≤ 25 := by
    by_cases h0 : f0 = 0
    · simp [h0]
    · have hw0 : wdegBiDom wY f0 ≤ W_F := by
        simpa only [Nat.zero_mul, Nat.sub_zero] using wdegBiDom_le_of_wdeg_coeff (le_of_eq hFwdeg) 0
      have h1 := wdegBiDom_ge_natDegree_mul wY f0 h0
      have hwY : wY = 1048575 := rfl
      have hWF_25 : 2 * W_F ≤ 51 * wY := by
        have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
        have := (div_le_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 2)).mp hWF_hi
        exact_mod_cast (show (2 : ℚ) * (W_F : ℚ) ≤ 51 * (wY : ℚ) by linarith)
      rw [hwY] at hw0 h1 hWF_25
      omega
  have hd1_le25 : f1.natDegree ≤ 25 := by
    have hw1 : wdegBiDom wY f1 + (wY - 1) ≤ W_F := by
      simpa only [one_mul] using wdegBiDom_coeff_le_of_wdeg (le_of_eq hFwdeg) 1 hf1_ne
    have h1 := wdegBiDom_ge_natDegree_mul wY f1 hf1_ne
    have hwY : wY = 1048575 := rfl
    have hWF_25 : 2 * W_F ≤ 51 * wY := by
      have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
      have := (div_le_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 2)).mp hWF_hi
      exact_mod_cast (show (2 : ℚ) * (W_F : ℚ) ≤ 51 * (wY : ℚ) by linarith)
    rw [hwY] at hw1 h1 hWF_25
    omega
  -- Split into Table 4 vs Table 1 globally based on `(f1.natDegree, f0.natDegree, W_F/wY)`!
  by_cases hT4 : f1.natDegree = 4 ∧ f0.natDegree ≤ 5 ∧ (W_F : ℚ) / (wY : ℚ) < 28 / 5
  · -- **TABLE 4 BRANCH (`d1 = 4, d0 ≤ 5, W_F / wY < 28 / 5`):**
    obtain ⟨hd1_4, hd0_5, hWF_28⟩ := hT4
    have ⟨hf0_ne, _, hres_d04⟩ := resY_f0_f1_ne_zero_of_irred_deg1 Fpoly hirr hFdeg (by change 1 ≤ f1.natDegree; omega)
    rw [hd1_4] at hres_d04
    let R54 := Polynomial.resultant f0 f1 5 4
    have hR54_ne : R54 ≠ 0 := resultant_54_ne_zero hd0_5 hd1_4 hf1_ne hres_d04
    have hR54_degZ : ∀ a, (R54.coeff a).natDegree ≤ 9 * D_ZF := fun a => by
      have h9 : (5 + 4) * D_ZF = 9 * D_ZF := by ring
      rw [← h9]
      exact degZ_resultant_biPoly_le f0 f1 5 4 D_ZF hf0_degZ hf1_degZ a
    have hWF_5lo : 5 * wY ≤ W_F + 1 := by
      have hw1 : wdegBiDom wY f1 + (wY - 1) ≤ W_F := by
        simpa only [one_mul] using wdegBiDom_coeff_le_of_wdeg (le_of_eq hFwdeg) 1 hf1_ne
      have h1 := wdegBiDom_ge_natDegree_mul wY f1 hf1_ne
      rw [hd1_4] at h1
      have hw : 1 ≤ wY := by norm_num [wY]
      omega
    have hWF_6hi : W_F + 1 < 6 * wY := by
      have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
      have hmul : (W_F : ℚ) * 5 < 28 * (wY : ℚ) := by
        have := (div_lt_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 5)).mp hWF_28; linarith
      have hnat : W_F * 5 < 28 * wY := by exact_mod_cast hmul
      have hw : wY = 1048575 := rfl; omega
    -- Peel off `S_deg`: `f1_z.natDegree ≠ 4` or `R54(z) = 0` (at most `10 * D_ZF` points!)
    let S_bad1 := S.filter fun z => (evalZBiPoly f1 z).natDegree ≠ 4
    let S_bad2 := S.filter fun z => R54.map (Polynomial.evalRingHom z) = 0
    let S_t4 := S.filter fun z => (evalZBiPoly f1 z).natDegree = 4 ∧ R54.map (Polynomial.evalRingHom z) ≠ 0
    have hbad1_card : S_bad1.card ≤ D_ZF := by
      simpa [S_bad1, hd1_4] using card_evalZBiPoly_natDegree_lt_le f1 hf1_ne hf1_degZ S
    have hbad2_card : S_bad2.card ≤ 9 * D_ZF := card_evalZ_poly_eq_zero_le R54 hR54_ne hR54_degZ S
    have hS_split : S.card ≤ S_t4.card + 10 * D_ZF := by
      have hsub : S ⊆ S_t4 ∪ (S_bad1 ∪ S_bad2) := by
        intro z hz; simp only [Finset.mem_union, S_t4, S_bad1, S_bad2, Finset.mem_filter]
        by_cases h1 : (evalZBiPoly f1 z).natDegree = 4
        · by_cases h2 : R54.map (Polynomial.evalRingHom z) = 0
          · exact Or.inr (Or.inr ⟨hz, h2⟩)
          · exact Or.inl ⟨hz, h1, h2⟩
        · exact Or.inr (Or.inl ⟨hz, h1⟩)
      calc S.card ≤ (S_t4 ∪ (S_bad1 ∪ S_bad2)).card := Finset.card_le_card hsub
        _ ≤ S_t4.card + (S_bad1 ∪ S_bad2).card := Finset.card_union_le _ _
        _ ≤ S_t4.card + (S_bad1.card + S_bad2.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
        _ ≤ S_t4.card + 10 * D_ZF := by omega
    -- Constructor for `KerD45Data` at any `z ∈ S_t4`!
    let mkD (z : Fld) (hz : z ∈ S_t4) : KerD45Data :=
      have hzS : z ∈ S := (Finset.mem_filter.mp hz).1
      have hdeg4 : (evalZBiPoly f1 z).natDegree = 4 := (Finset.mem_filter.mp hz).2.1
      have hRne : R54.map (Polynomial.evalRingHom z) ≠ 0 := (Finset.mem_filter.mp hz).2.2
      have hFz_eq : evalZContact Fpoly z = ∑ e : KerDIdx wY W_F 1, cC ((f_coord e).eval z) * kerDBasisPoly e.1 :=
        evalZContact_sum_kerD f_coord z
      have hf1z_eq : (∑ e : KerDIdx wY W_F 1, cC ((f_coord e).eval z) * kerDBasisPoly e.1).coeff 1 = evalZBiPoly f1 z := by
        rw [← hFz_eq]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f1]
      have hf0z_eq : (∑ e : KerDIdx wY W_F 1, cC ((f_coord e).eval z) * kerDBasisPoly e.1).coeff 0 = evalZBiPoly f0 z := by
        rw [← hFz_eq]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f0]
      { W_F := W_F
        hWF_lo := hWF_5lo
        hWF_hi := hWF_6hi
        f_coord := fun e => (f_coord e).eval z
        y := fun i => u₀ i + z ^ q₀ * u₁ i
        k := k
        hvan := hvan_z z
        P := P z
        hPdeg := hP z hzS
        Az := Az z
        hAz_card := hcard z hzS
        hagree := fun i hi => (hmatch z hzS i).mp hi
        hFvan := by rw [← hFz_eq]; exact hFvan z hzS
        hf1_deg := by rw [hf1z_eq]; exact hdeg4
        hRes_ne := by
          rw [hf0z_eq, hf1z_eq]
          have hm := Polynomial.resultant_map_map f0 f1 5 4 (Polynomial.mapRingHom (Polynomial.evalRingHom z))
          dsimp only [R54] at hRne
          rw [← Polynomial.coe_mapRingHom, ← hm] at hRne
          exact hRne }
    -- Helper: bound any subset `S_clean ⊆ S_t4` where EVERY `z ∈ S_clean` has `T4SingleWitness ∨ T4Std5Witness (std5Slot (G_val))`!
    have hbound_clean : ∀ S_clean : Finset Fld, S_clean ⊆ S_t4 →
        (∀ z (hz : z ∈ S_clean),
          T4SingleWitness W_F k ∨ T4Std5Witness W_F k (std5Slot (G_val W_F k (Az z)))) →
        (S_clean.card : ℚ) ≤
          if q₀ = 1 then (T4_C1_SUM : ℚ) * (D_ZF : ℚ) + (T4_C0_SUM : ℚ)
          else (T4_Q2_SUM : ℚ) := by
      intro S_clean hsub hwit
      have hS_clean_S : ∀ z ∈ S_clean, z ∈ S := fun z hz => (Finset.mem_filter.mp (hsub hz)).1
      by_cases hsing : T4SingleWitness W_F k
      · obtain ⟨m, s, cHiN, cHiD, δN, δD, w1, w2, hm, _, hs, _, hcHiD, hδN, hδD, hcHi, hsurp, hc1, hc2, hp1, hp2, hb1, hb0, hbq2⟩ := hsing
        rcases hq₀ with rfl | rfl
        · simp only [↓reduceIte]
          have hcard1 := card_le_of_quotient_surplus u₀ u₁ w1 hc1 (Or.inl rfl) le_rfl hs hm hcHiD hδN hδD (by omega)
            hWF_lo hcHi f_coord hirr hFdeg hFwdeg hf_wYZ k (fun i => ⟨(hk_exact i).1, (hk_exact i).2 m⟩)
            hsurp S_clean P Az (fun z hz => hP z (hS_clean_S z hz)) (fun z hz => hFvan z (hS_clean_S z hz))
            (fun z hz => hcard z (hS_clean_S z hz)) (fun z hz => hmatch z (hS_clean_S z hz))
            (fun z hz => hbad z (hS_clean_S z hz)) (fun h => by rw [hp1] at h; cases h)
          have h1 : (w1.c1Bkt : ℚ) ≤ (T4_C1_SUM : ℚ) := by exact_mod_cast (hb1.trans single_le_sum.1)
          have h0 : (w1.c0Bkt : ℚ) ≤ (T4_C0_SUM : ℚ) := by exact_mod_cast (hb0.trans single_le_sum.2.1)
          have hDZ0 : (0 : ℚ) ≤ (D_ZF : ℚ) := Nat.cast_nonneg D_ZF
          have hmul := mul_le_mul_of_nonneg_right h1 hDZ0
          linarith only [hcard1, hmul, h0]
        · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
          have hDZ3850 : D_ZF ≤ 3850 := (hq2_cond rfl).2
          have hcard2 := card_le_of_quotient_surplus u₀ u₁ w2 hc2 (Or.inr rfl) le_rfl hs hm hcHiD hδN hδD (by omega)
            hWF_lo hcHi f_coord hirr hFdeg hFwdeg hf_wYZ k (fun i => ⟨(hk_exact i).1, (hk_exact i).2 m⟩)
            hsurp S_clean P Az (fun z hz => hP z (hS_clean_S z hz)) (fun z hz => hFvan z (hS_clean_S z hz))
            (fun z hz => hcard z (hS_clean_S z hz)) (fun z hz => hmatch z (hS_clean_S z hz))
            (fun z hz => hbad z (hS_clean_S z hz)) (fun h => by rw [hp2] at h; cases h)
          have hq : (w2.c1Bkt : ℚ) * (D_ZF : ℚ) + (w2.c0Bkt : ℚ) ≤ (T4_Q2_SUM : ℚ) := by
            have hDZQ : (D_ZF : ℚ) ≤ 3850 := by exact_mod_cast hDZ3850
            have hle : (w2.c1Bkt : ℚ) * 3850 + (w2.c0Bkt : ℚ) ≤ (T4_Q2_SUM : ℚ) := by
              exact_mod_cast (hbq2.trans single_le_sum.2.2)
            have hmul := mul_le_mul_of_nonneg_left hDZQ (Nat.cast_nonneg (α := ℚ) w2.c1Bkt)
            linarith only [hmul, hle]
          exact hcard2.trans hq
      · -- Partition `S_clean` across the 5 universal `STD5` slots!
        let Sr (r : Fin 5) : Finset Fld := S_clean.filter fun z => std5Slot (G_val W_F k (Az z)) = r
        have hpart : S_clean.card ≤ ∑ r : Fin 5, (Sr r).card := by
          have hsub_u : S_clean ⊆ Finset.univ.biUnion Sr := by
            intro z hz; exact Finset.mem_biUnion.mpr ⟨std5Slot (G_val W_F k (Az z)), Finset.mem_univ _,
              Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
          exact (Finset.card_le_card hsub_u).trans Finset.card_biUnion_le
        have hSr_le : ∀ r : Fin 5, ((Sr r).card : ℚ) ≤
            if q₀ = 1 then (std5C1 r : ℚ) * (D_ZF : ℚ) + (std5C0 r : ℚ)
            else (std5Q2 r : ℚ) := by
          intro r
          by_cases hemp : (Sr r).Nonempty
          · obtain ⟨zr, hzr⟩ := hemp
            have hzr_clean : zr ∈ S_clean := (Finset.mem_filter.mp hzr).1
            have hzr_slot : std5Slot (G_val W_F k (Az zr)) = r := (Finset.mem_filter.mp hzr).2
            have hw_r : T4Std5Witness W_F k r := by
              rw [← hzr_slot]; exact (hwit zr hzr_clean).resolve_left hsing
            obtain ⟨m, s, cHiN, cHiD, δN, δD, w1, w2, hm, _, hs, _, hcHiD, hδN, hδD, hhiGD, hcHi, hsurp,
              hc1, hc2, hnop64, hb1, hb0, hbq2⟩ := hw_r
            have hSr_S : ∀ z ∈ Sr r, z ∈ S := fun z hz => hS_clean_S z (Finset.mem_filter.mp hz).1
            have hp64_ok : ∀ (w : CapWitness), ((std5Bounds r).2.2.1 = (std5Bounds r).2.2.2 → w.useP64 = false) →
                w.useP64 = true → 1 = 1 ∧ ∀ z ∈ Sr r,
                  ((std5Bounds r).2.2.2 : ℤ) * ((W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) - ∑ i ∈ Az z, (2 * (k i : ℤ) - 1)) ≤
                    ((std5Bounds r).2.2.1 * N : ℤ) := by
              intro w hno huse
              refine ⟨rfl, fun z hz => ?_⟩
              have hz_t4 : z ∈ S_t4 := hsub (Finset.mem_filter.mp hz).1
              have hz_slot : std5Slot (G_val W_F k (Az z)) = r := (Finset.mem_filter.mp hz).2
              have hGnn : 0 ≤ G_val W_F k (Az z) := G_val_nonneg (mkD z hz_t4)
              have hspec := std5Slot_spec hGnn
              dsimp only at hspec; rw [hz_slot] at hspec
              have hlt : (std5Bounds r).2.2.1 < (std5Bounds r).2.2.2 := by
                have hle : (std5Bounds r).2.2.1 ≤ (std5Bounds r).2.2.2 := by fin_cases r <;> decide
                have hne : (std5Bounds r).2.2.1 ≠ (std5Bounds r).2.2.2 := fun heq => by
                  rw [hno heq] at huse; cases huse
                omega
              have h1 := hspec.2.2.2 hlt
              have h2 := sum_2k_sub_1_le_G_val W_F k (Az z)
              have hpos : (0 : ℤ) ≤ ((std5Bounds r).2.2.2 : ℤ) := Nat.cast_nonneg _
              have hmul := mul_le_mul_of_nonneg_left h2 hpos
              linarith only [h1, hmul]
            rcases hq₀ with rfl | rfl
            · simp only [↓reduceIte]
              have hcard1 := card_le_of_quotient_surplus u₀ u₁ w1 hc1 (Or.inl rfl) le_rfl hs hm hcHiD hδN hδD hhiGD
                hWF_lo hcHi f_coord hirr hFdeg hFwdeg hf_wYZ k (fun i => ⟨(hk_exact i).1, (hk_exact i).2 m⟩)
                hsurp (Sr r) P Az (fun z hz => hP z (hSr_S z hz)) (fun z hz => hFvan z (hSr_S z hz))
                (fun z hz => hcard z (hSr_S z hz)) (fun z hz => hmatch z (hSr_S z hz))
                (fun z hz => hbad z (hSr_S z hz)) (hp64_ok w1 (fun heq => (hnop64 heq).1))
              have h1 : (w1.c1Bkt : ℚ) ≤ (std5C1 r : ℚ) := by exact_mod_cast hb1
              have h0 : (w1.c0Bkt : ℚ) ≤ (std5C0 r : ℚ) := by exact_mod_cast hb0
              have hDZ0 : (0 : ℚ) ≤ (D_ZF : ℚ) := Nat.cast_nonneg D_ZF
              have hmul := mul_le_mul_of_nonneg_right h1 hDZ0
              linarith only [hcard1, hmul, h0]
            · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
              have hDZ3850 : D_ZF ≤ 3850 := (hq2_cond rfl).2
              have hcard2 := card_le_of_quotient_surplus u₀ u₁ w2 hc2 (Or.inr rfl) le_rfl hs hm hcHiD hδN hδD hhiGD
                hWF_lo hcHi f_coord hirr hFdeg hFwdeg hf_wYZ k (fun i => ⟨(hk_exact i).1, (hk_exact i).2 m⟩)
                hsurp (Sr r) P Az (fun z hz => hP z (hSr_S z hz)) (fun z hz => hFvan z (hSr_S z hz))
                (fun z hz => hcard z (hSr_S z hz)) (fun z hz => hmatch z (hSr_S z hz))
                (fun z hz => hbad z (hSr_S z hz)) (hp64_ok w2 (fun heq => (hnop64 heq).2))
              have hq : (w2.c1Bkt : ℚ) * (D_ZF : ℚ) + (w2.c0Bkt : ℚ) ≤ (std5Q2 r : ℚ) := by
                have hDZQ : (D_ZF : ℚ) ≤ 3850 := by exact_mod_cast hDZ3850
                have hle : (w2.c1Bkt : ℚ) * 3850 + (w2.c0Bkt : ℚ) ≤ (std5Q2 r : ℚ) := by exact_mod_cast hbq2
                have hmul := mul_le_mul_of_nonneg_left hDZQ (Nat.cast_nonneg (α := ℚ) w2.c1Bkt)
                linarith only [hmul, hle]
              exact hcard2.trans hq
          · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty, Nat.cast_zero]
            split_ifs <;> positivity
        have hpartQ : (S_clean.card : ℚ) ≤ ∑ r : Fin 5, ((Sr r).card : ℚ) := by exact_mod_cast hpart
        rcases hq₀ with rfl | rfl
        · simp only [↓reduceIte] at hSr_le ⊢
          calc (S_clean.card : ℚ) ≤ ∑ r : Fin 5, ((std5C1 r : ℚ) * (D_ZF : ℚ) + (std5C0 r : ℚ)) :=
                hpartQ.trans (Finset.sum_le_sum fun r _ => hSr_le r)
            _ = (∑ r : Fin 5, (std5C1 r : ℚ)) * (D_ZF : ℚ) + ∑ r : Fin 5, (std5C0 r : ℚ) := by
                rw [Finset.sum_add_distrib, Finset.sum_mul]
            _ = (T4_C1_SUM : ℚ) * (D_ZF : ℚ) + (T4_C0_SUM : ℚ) := by
                rw [← Nat.cast_sum, ← Nat.cast_sum, sum_std5C1, sum_std5C0]
        · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at hSr_le ⊢
          calc (S_clean.card : ℚ) ≤ ∑ r : Fin 5, (std5Q2 r : ℚ) :=
                hpartQ.trans (Finset.sum_le_sum fun r _ => hSr_le r)
            _ = (T4_Q2_SUM : ℚ) := by rw [← Nat.cast_sum, sum_std5Q2]
    -- Now analyze the global `3 × 3` matrix `MZ` over `Fld[Z][T]`!
    let MZ : Matrix (Fin 3) (Fin 3) (Polynomial (Polynomial Fld)) := Matrix.of fun j c =>
      match c with
      | ⟨0, _⟩ => PjZ f_coord j
      | ⟨1, _⟩ => CjZ f_coord j
      | ⟨2, _⟩ => BjZ f_coord j
    have hMZ_map : ∀ z (hz : z ∈ S_t4), MZ.det.map (Polynomial.evalRingHom z) = (mkD z hz).detM := by
      intro z hz
      rw [← Polynomial.coe_mapRingHom, RingHom.map_det (Polynomial.mapRingHom (Polynomial.evalRingHom z)) MZ]
      unfold KerD45Data.detM KerD45Data.coeffMat
      congr 1; apply Matrix.ext; intro j c; fin_cases c
      · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, MZ, Matrix.of_apply, Polynomial.coe_mapRingHom]
        exact map_PjZ f_coord j z (mkD z hz) rfl (fun _ => rfl)
      · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, MZ, Matrix.of_apply, Polynomial.coe_mapRingHom]
        exact map_CjZ f_coord j z (mkD z hz) rfl (fun _ => rfl)
      · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, MZ, Matrix.of_apply, Polynomial.coe_mapRingHom]
        exact map_BjZ f_coord j z (mkD z hz) rfl (fun _ => rfl)
    by_cases hdetZ : MZ.det ≠ 0
    · -- Subcase 1: `MZ.det ≠ 0` globally → at most `3 * D_ZF` roots where `detM_z = 0`!
      have hdet_degZ : ∀ a, (MZ.det.coeff a).natDegree ≤ 3 * D_ZF := by
        intro a; rw [Matrix.det_apply, finset_sum_coeff]
        refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
        dsimp only [Function.comp_apply]
        have hsmul : ∀ (u : ℤˣ) (p : Polynomial (Polynomial Fld)),
            ((u • p).coeff a).natDegree ≤ (p.coeff a).natDegree := fun u p => by
          rw [Units.smul_def]; rcases Int.units_eq_one_or u with rfl | rfl <;> simp
        refine (hsmul _ _).trans ?_
        refine (degZ_prod_poly_le Finset.univ (fun i => MZ (σ i) i) D_ZF (fun i _ b => ?_) a).trans (by simp)
        dsimp only [MZ, Matrix.of_apply]; fin_cases i
        · exact degZ_PjZ_le f_coord hfc_deg _ b
        · exact degZ_CjZ_le f_coord hfc_deg _ b
        · exact degZ_BjZ_le f_coord hfc_deg _ b
      let S_clean := S_t4.filter fun z => MZ.det.map (Polynomial.evalRingHom z) ≠ 0
      have hbad_det : (S_t4.filter fun z => MZ.det.map (Polynomial.evalRingHom z) = 0).card ≤ 3 * D_ZF :=
        card_evalZ_poly_eq_zero_le MZ.det hdetZ hdet_degZ S_t4
      have hsplit_t4 : S_t4.card ≤ S_clean.card + 3 * D_ZF := by
        have hsub : S_t4 ⊆ S_clean ∪ (S_t4.filter fun z => MZ.det.map (Polynomial.evalRingHom z) = 0) := by
          intro z hz; simp only [Finset.mem_union, S_clean, Finset.mem_filter]
          by_cases h0 : MZ.det.map (Polynomial.evalRingHom z) = 0
          · exact Or.inr ⟨hz, h0⟩
          · exact Or.inl ⟨hz, h0⟩
        have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        omega
      have hcl := hbound_clean S_clean (Finset.filter_subset _ _) (fun z hz => by
        have hzt4 : z ∈ S_t4 := (Finset.mem_filter.mp hz).1
        have hne : (mkD z hzt4).detM ≠ 0 := by rw [← hMZ_map z hzt4]; exact (Finset.mem_filter.mp hz).2
        exact t4_point_det_witness (mkD z hzt4) hWF_28.le hne)
      have htot : (S.card : ℚ) ≤ (S_clean.card : ℚ) + 13 * (D_ZF : ℚ) := by
        have : S.card ≤ S_clean.card + 13 * D_ZF := by omega
        exact_mod_cast this
      rcases hq₀ with rfl | rfl
      · simp only [↓reduceIte] at hcl ⊢; push_cast; linarith [Nat.cast_nonneg (α := ℚ) D_ZF]
      · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at hcl ⊢
        have hDZQ : (D_ZF : ℚ) ≤ 3850 := by exact_mod_cast (hq2_cond rfl).2
        push_cast; linarith
    · -- Subcase 2: `MZ.det = 0` globally! Check the 3 `(C, B)` minors!
      push Not at hdetZ
      let minorCB (r1 r2 : Fin 3) : Polynomial (Polynomial Fld) :=
        CjZ f_coord r1 * BjZ f_coord r2 + CjZ f_coord r2 * BjZ f_coord r1
      by_cases hmin_ex : ∃ r1 r2 : Fin 3, minorCB r1 r2 ≠ 0
      · -- Subcase 2a: some `(C, B)` minor `pZ := minorCB r1 r2 ≠ 0`!
        obtain ⟨r1, r2, hpZ_ne⟩ := hmin_ex
        let pZ := minorCB r1 r2
        let cZ := PjZ f_coord r1 * BjZ f_coord r2 + PjZ f_coord r2 * BjZ f_coord r1
        let bZ := PjZ f_coord r1 * CjZ f_coord r2 + PjZ f_coord r2 * CjZ f_coord r1
        have hpZ_degZ : ∀ a, (pZ.coeff a).natDegree ≤ 2 * D_ZF := fun a => by
          dsimp only [pZ, minorCB]; rw [Polynomial.coeff_add]
          refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
          · simpa [two_mul] using degZ_mul_poly_le (degZ_CjZ_le f_coord hfc_deg r1) (degZ_BjZ_le f_coord hfc_deg r2) a
          · simpa [two_mul] using degZ_mul_poly_le (degZ_CjZ_le f_coord hfc_deg r2) (degZ_BjZ_le f_coord hfc_deg r1) a
        have hcZ_degZ : ∀ a, (cZ.coeff a).natDegree ≤ 2 * D_ZF := fun a => by
          dsimp only [cZ]; rw [Polynomial.coeff_add]
          refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
          · simpa [two_mul] using degZ_mul_poly_le (degZ_PjZ_le f_coord hfc_deg r1) (degZ_BjZ_le f_coord hfc_deg r2) a
          · simpa [two_mul] using degZ_mul_poly_le (degZ_PjZ_le f_coord hfc_deg r2) (degZ_BjZ_le f_coord hfc_deg r1) a
        have hbZ_degZ : ∀ a, (bZ.coeff a).natDegree ≤ 2 * D_ZF := fun a => by
          dsimp only [bZ]; rw [Polynomial.coeff_add]
          refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
          · simpa [two_mul] using degZ_mul_poly_le (degZ_PjZ_le f_coord hfc_deg r1) (degZ_CjZ_le f_coord hfc_deg r2) a
          · simpa [two_mul] using degZ_mul_poly_le (degZ_PjZ_le f_coord hfc_deg r2) (degZ_CjZ_le f_coord hfc_deg r1) a
        have hsyzZ : ∀ j : Fin 3, pZ * PjZ f_coord j + cZ * CjZ f_coord j + bZ * BjZ f_coord j = 0 := by
          have hdet_sum := char2_det3_eq_sum MZ
          rw [hdetZ] at hdet_sum
          have hcf := char2_det3_cofactor_syzygy
            (PjZ f_coord 0) (PjZ f_coord 1) (PjZ f_coord 2)
            (CjZ f_coord 0) (CjZ f_coord 1) (CjZ f_coord 2)
            (BjZ f_coord 0) (BjZ f_coord 1) (BjZ f_coord 2)
            (by simpa [MZ] using hdet_sum.symm) r1 r2
          intro j
          have hPeq : ∀ i : Fin 3, (![PjZ f_coord 0, PjZ f_coord 1, PjZ f_coord 2] : Fin 3 → _) i = PjZ f_coord i := fun i => by fin_cases i <;> rfl
          have hCeq : ∀ i : Fin 3, (![CjZ f_coord 0, CjZ f_coord 1, CjZ f_coord 2] : Fin 3 → _) i = CjZ f_coord i := fun i => by fin_cases i <;> rfl
          have hBeq : ∀ i : Fin 3, (![BjZ f_coord 0, BjZ f_coord 1, BjZ f_coord 2] : Fin 3 → _) i = BjZ f_coord i := fun i => by fin_cases i <;> rfl
          simpa [pZ, minorCB, cZ, bZ, hPeq, hCeq, hBeq] using hcf j
        let UZ : BiPoly (Polynomial Fld) := makeEscapeUZ pZ cZ bZ
        let S_p0 := S_t4.filter fun z => pZ.map (Polynomial.evalRingHom z) = 0
        let S_esc := S_t4.filter fun z => triEval UZ z (P z) = 0
        let S_clean := S_t4.filter fun z => pZ.map (Polynomial.evalRingHom z) ≠ 0 ∧ triEval UZ z (P z) ≠ 0
        have hp0_card : S_p0.card ≤ 2 * D_ZF := card_evalZ_poly_eq_zero_le pZ hpZ_ne hpZ_degZ S_t4
        have hesc_card : (S_esc.card : ℚ) ≤ max ((2 * D_ZF : ℕ) : ℚ) (arklibBoundPowQ q₀ 1 (2 * D_ZF)) :=
          card_le_of_biPoly_pow u₀ u₁ q₀ (by rcases hq₀ with rfl | rfl <;> omega)
            UZ 1 (2 * D_ZF) (makeEscapeUZ_ne_zero hpZ_ne) (makeEscapeUZ_natDegree_le pZ cZ bZ)
            (makeEscapeUZ_degZ_le hpZ_degZ hcZ_degZ hbZ_degZ)
            S_esc P Az
            (fun z hz => hP z (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1)
            (fun z hz => (Finset.mem_filter.mp hz).2)
            (fun z hz => hcard z (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1)
            (fun z hz i hi => (hmatch z (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1 i).mp hi)
            (fun z hz => hbad z (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1)
        have hsplit_t4 : S_t4.card ≤ S_clean.card + S_p0.card + S_esc.card := by
          have hsub : S_t4 ⊆ S_clean ∪ (S_p0 ∪ S_esc) := by
            intro z hz; simp only [Finset.mem_union, S_clean, S_p0, S_esc, Finset.mem_filter]
            by_cases h1 : pZ.map (Polynomial.evalRingHom z) = 0
            · exact Or.inr (Or.inl ⟨hz, h1⟩)
            · by_cases h2 : triEval UZ z (P z) = 0
              · exact Or.inr (Or.inr ⟨hz, h2⟩)
              · exact Or.inl ⟨hz, h1, h2⟩
          calc S_t4.card ≤ (S_clean ∪ (S_p0 ∪ S_esc)).card := Finset.card_le_card hsub
            _ ≤ S_clean.card + (S_p0 ∪ S_esc).card := Finset.card_union_le _ _
            _ ≤ S_clean.card + (S_p0.card + S_esc.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
            _ = S_clean.card + S_p0.card + S_esc.card := by omega
        -- On `S_clean`, `EscapeUZero` is IMPOSSIBLE by `syzygy_prop_of_minor_ne_zero`!
        have hcl := hbound_clean S_clean (Finset.filter_subset _ _) (fun z hz => by
          have hzt4 : z ∈ S_t4 := (Finset.mem_filter.mp hz).1
          have hpz_ne : pZ.map (Polynomial.evalRingHom z) ≠ 0 := (Finset.mem_filter.mp hz).2.1
          have hUz_ne : triEval UZ z (P z) ≠ 0 := (Finset.mem_filter.mp hz).2.2
          rcases t4_point_dichotomy (mkD z hzt4) hWF_28.le with ⟨pz, cz, bz, hpz0, _, hsyz_z, hUP0⟩ | hw
          · exfalso; apply hUz_ne
            rw [triEval_makeEscapeUZ]
            have hm_syz : ∀ j : Fin 3,
                pZ.map (Polynomial.evalRingHom z) * (mkD z hzt4).Pj j +
                cZ.map (Polynomial.evalRingHom z) * (mkD z hzt4).Cj j +
                bZ.map (Polynomial.evalRingHom z) * (mkD z hzt4).Bj j = 0 := fun j => by
              have h := congrArg (Polynomial.map (Polynomial.evalRingHom z)) (hsyzZ j)
              simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_zero,
                map_PjZ f_coord j z (mkD z hzt4) rfl (fun _ => rfl),
                map_CjZ f_coord j z (mkD z hzt4) rfl (fun _ => rfl),
                map_BjZ f_coord j z (mkD z hzt4) rfl (fun _ => rfl)] at h
              exact h
            have hΔ_ne : (mkD z hzt4).Cj r1 * (mkD z hzt4).Bj r2 + (mkD z hzt4).Cj r2 * (mkD z hzt4).Bj r1 ≠ 0 := by
              have h := hpz_ne
              dsimp only [pZ, minorCB] at h
              simpa only [Polynomial.map_add, Polynomial.map_mul,
                map_CjZ f_coord _ z (mkD z hzt4) rfl (fun _ => rfl),
                map_BjZ f_coord _ z (mkD z hzt4) rfl (fun _ => rfl)] using h
            have ⟨hprop_c, hprop_b⟩ := syzygy_prop_of_minor_ne_zero
              (hm_syz r1) (hm_syz r2) (hsyz_z r1) (hsyz_z r2) hΔ_ne
            have hpz_sq_ne : pz.comp (X ^ 2) ≠ 0 := fun h0 => hpz0 ((comp_X_sq_eq_zero_iff pz).mp h0)
            apply mul_left_cancel₀ hpz_sq_ne
            rw [mul_zero]
            have hpc_sq : (pZ.map (Polynomial.evalRingHom z)).comp (X ^ 2) * cz.comp (X ^ 2) =
                pz.comp (X ^ 2) * (cZ.map (Polynomial.evalRingHom z)).comp (X ^ 2) := by
              rw [← mul_comp, ← mul_comp, hprop_c]
            have hpb_sq : (pZ.map (Polynomial.evalRingHom z)).comp (X ^ 2) * bz.comp (X ^ 2) =
                pz.comp (X ^ 2) * (bZ.map (Polynomial.evalRingHom z)).comp (X ^ 2) := by
              rw [← mul_comp, ← mul_comp, hprop_b]
            have hUP0' : pz.comp (X ^ 2) * P z + bz.comp (X ^ 2) + X * cz.comp (X ^ 2) = 0 := hUP0
            linear_combination (pZ.map (Polynomial.evalRingHom z)).comp (X ^ 2) * hUP0' - hpb_sq - X * hpc_sq
          · exact hw)
        have htot : (S.card : ℚ) ≤ (S_clean.card : ℚ) + 12 * (D_ZF : ℚ) + (S_esc.card : ℚ) := by
          have : S.card ≤ S_clean.card + 12 * D_ZF + S_esc.card := by omega
          exact_mod_cast this
        rcases hq₀ with rfl | rfl
        · simp only [↓reduceIte] at hcl ⊢
          have hark := hesc_card.trans (card_le_of_biPoly_pow_1_bound D_ZF)
          push_cast; linarith [Nat.cast_nonneg (α := ℚ) D_ZF]
        · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at hcl ⊢
          have hDZ3850 : D_ZF ≤ 3850 := (hq2_cond rfl).2
          have hark := hesc_card.trans (card_le_of_biPoly_pow_2_bound hDZ3850)
          have hDZQ : (D_ZF : ℚ) ≤ 3850 := by exact_mod_cast hDZ3850
          push_cast; linarith
      · -- Subcase 2b: ALL `(C, B)` minors vanish globally → EVERY `z ∈ S_t4` satisfies `T4ABranch.p0Zero`!
        push Not at hmin_ex
        have hcl := hbound_clean S_t4 le_rfl (fun z hz => by
          refine t4_point_p0Zero_witness (mkD z hz) hWF_28.le (fun j => ?_)
          have h := congrArg (Polynomial.map (Polynomial.evalRingHom z)) (hmin_ex j 2)
          dsimp only [minorCB] at h
          simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_zero,
            map_CjZ f_coord _ z (mkD z hz) rfl (fun _ => rfl),
            map_BjZ f_coord _ z (mkD z hz) rfl (fun _ => rfl)] at h
          linear_combination h)
        have htot : (S.card : ℚ) ≤ (S_t4.card : ℚ) + 10 * (D_ZF : ℚ) := by exact_mod_cast hS_split
        rcases hq₀ with rfl | rfl
        · simp only [↓reduceIte] at hcl ⊢; push_cast; linarith [Nat.cast_nonneg (α := ℚ) D_ZF]
        · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at hcl ⊢
          have hDZQ : (D_ZF : ℚ) ≤ 3850 := by exact_mod_cast (hq2_cond rfl).2
          push_cast; linarith
  · -- **TABLE 1 BRANCH (`¬ (d1 = 4 ∧ d0 ≤ 5 ∧ W_F / wY < 28 / 5)`):**
    -- Peel off `f0_z.natDegree ≠ d0`, `¬(f1_z ≠ 0 ∧ f1_z.natDegree = d1)`, and (when `d1 ≥ 2`) `Res_Y(f0_z, f1_z) = 0`!
    let S_clean : Finset Fld :=
      if hd1 : 2 ≤ f1.natDegree then
        S.filter fun z =>
          (evalZBiPoly f0 z).natDegree = f0.natDegree ∧
          (evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree) ∧
          (Polynomial.resultant f0 f1 f0.natDegree f1.natDegree).map (Polynomial.evalRingHom z) ≠ 0
      else
        S.filter fun z =>
          (evalZBiPoly f0 z).natDegree = f0.natDegree ∧
          (evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree)
    have hS_split : S.card ≤ S_clean.card + 52 * D_ZF := by
      dsimp only [S_clean]
      split_ifs with hd1
      · have ⟨hf0_ne, _, hres_ne⟩ := resY_f0_f1_ne_zero_of_irred_deg1 Fpoly hirr hFdeg (by change 1 ≤ f1.natDegree; omega)
        let B0 := S.filter fun z => (evalZBiPoly f0 z).natDegree ≠ f0.natDegree
        let B1 := S.filter fun z => ¬ (evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree)
        let B2 := S.filter fun z => (Polynomial.resultant f0 f1 f0.natDegree f1.natDegree).map (Polynomial.evalRingHom z) = 0
        have hB0 : B0.card ≤ D_ZF := card_evalZBiPoly_natDegree_lt_le f0 hf0_ne hf0_degZ S
        have hB1 : B1.card ≤ D_ZF := card_evalZBiPoly_good_deg_le f1 hf1_ne hf1_degZ S
        have hB2 : B2.card ≤ (f0.natDegree + f1.natDegree) * D_ZF :=
          card_evalZ_poly_eq_zero_le _ hres_ne (degZ_resultant_biPoly_le f0 f1 f0.natDegree f1.natDegree D_ZF hf0_degZ hf1_degZ) S
        have hsub : S ⊆ (S.filter fun z => (evalZBiPoly f0 z).natDegree = f0.natDegree ∧
            (evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree) ∧
            (Polynomial.resultant f0 f1 f0.natDegree f1.natDegree).map (Polynomial.evalRingHom z) ≠ 0) ∪ (B0 ∪ (B1 ∪ B2)) := by
          intro z hz; simp only [Finset.mem_union, B0, B1, B2, Finset.mem_filter]
          by_cases h0 : (evalZBiPoly f0 z).natDegree = f0.natDegree
          · by_cases h1 : evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree
            · by_cases h2 : (Polynomial.resultant f0 f1 f0.natDegree f1.natDegree).map (Polynomial.evalRingHom z) = 0
              · exact Or.inr (Or.inr (Or.inr ⟨hz, h2⟩))
              · exact Or.inl ⟨hz, h0, h1, h2⟩
            · exact Or.inr (Or.inr (Or.inl ⟨hz, h1⟩))
          · exact Or.inr (Or.inl ⟨hz, h0⟩)
        have hle := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_left ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)) _))
        have : (f0.natDegree + f1.natDegree) * D_ZF ≤ 50 * D_ZF := Nat.mul_le_mul_right D_ZF (by omega)
        omega
      · let B0 := S.filter fun z => (evalZBiPoly f0 z).natDegree ≠ f0.natDegree
        let B1 := S.filter fun z => ¬ (evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree)
        have hB0 : B0.card ≤ D_ZF := by
          by_cases hf0_ne : f0 = 0
          · dsimp only [B0]; rw [hf0_ne]; simp [evalZBiPoly]
          · exact card_evalZBiPoly_natDegree_lt_le f0 hf0_ne hf0_degZ S
        have hB1 : B1.card ≤ D_ZF := card_evalZBiPoly_good_deg_le f1 hf1_ne hf1_degZ S
        have hsub : S ⊆ (S.filter fun z => (evalZBiPoly f0 z).natDegree = f0.natDegree ∧
            (evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree)) ∪ (B0 ∪ B1) := by
          intro z hz; simp only [Finset.mem_union, B0, B1, Finset.mem_filter]
          by_cases h0 : (evalZBiPoly f0 z).natDegree = f0.natDegree
          · by_cases h1 : evalZBiPoly f1 z ≠ 0 ∧ (evalZBiPoly f1 z).natDegree = f1.natDegree
            · exact Or.inl ⟨hz, h0, h1⟩
            · exact Or.inr (Or.inr ⟨hz, h1⟩)
          · exact Or.inr (Or.inl ⟨hz, h0⟩)
        have hle := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_left (Finset.card_union_le _ _) _))
        omega
    have hS_clean_sub : S_clean ⊆ S := by dsimp only [S_clean]; split_ifs <;> exact Finset.filter_subset _ _
    have hcl : (S_clean.card : ℚ) ≤
        if q₀ = 1 then (T4_C1_SUM : ℚ) * (D_ZF : ℚ) + (T4_C0_SUM : ℚ) else (T4_Q2_SUM : ℚ) := by
      by_cases hemp : S_clean.Nonempty
      · obtain ⟨z0, hz0⟩ := hemp
        have hz0S : z0 ∈ S := hS_clean_sub hz0
        have hFz0 : evalZContact Fpoly z0 = ∑ e : KerDIdx wY W_F 1, cC ((f_coord e).eval z0) * kerDBasisPoly e.1 :=
          evalZContact_sum_kerD f_coord z0
        have hf0z : (∑ e : KerDIdx wY W_F 1, cC ((f_coord e).eval z0) * kerDBasisPoly e.1).coeff 0 = evalZBiPoly f0 z0 := by
          rw [← hFz0]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f0]
        have hf1z : (∑ e : KerDIdx wY W_F 1, cC ((f_coord e).eval z0) * kerDBasisPoly e.1).coeff 1 = evalZBiPoly f1 z0 := by
          rw [← hFz0]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f1]
        have ⟨hd0z, hf1z_ne, hd1z, hresz⟩ :
            (evalZBiPoly f0 z0).natDegree = f0.natDegree ∧
            evalZBiPoly f1 z0 ≠ 0 ∧
            (evalZBiPoly f1 z0).natDegree = f1.natDegree ∧
            (2 ≤ (evalZBiPoly f1 z0).natDegree →
              Polynomial.resultant (evalZBiPoly f0 z0) (evalZBiPoly f1 z0)
                (evalZBiPoly f0 z0).natDegree (evalZBiPoly f1 z0).natDegree ≠ 0) := by
          dsimp only [S_clean] at hz0
          split_ifs at hz0 with hd1
          · obtain ⟨_, h0, ⟨hne1, h1⟩, h2⟩ := Finset.mem_filter.mp hz0
            refine ⟨h0, hne1, h1, fun _ => ?_⟩
            rw [h0, h1]
            have hm := Polynomial.resultant_map_map f0 f1 f0.natDegree f1.natDegree
              (Polynomial.mapRingHom (Polynomial.evalRingHom z0))
            rw [← Polynomial.coe_mapRingHom, ← hm] at h2
            exact h2
          · obtain ⟨_, h0, ⟨hne1, h1⟩⟩ := Finset.mem_filter.mp hz0
            exact ⟨h0, hne1, h1, fun hge => by omega⟩
        obtain ⟨c, hc_mem, _, hmpos, _, _, _, hcHi, hsurp, hcap1, hc1_le, hc0_le, hcap2_fn⟩ :=
          t1_surplus_of_point (fun e => (f_coord e).eval z0) (fun i => u₀ i + z0 ^ q₀ * u₁ i) k
            (hvan_z z0) (P z0) (hP z0 hz0S) (Az z0) (hcard z0 hz0S)
            (fun i hi => (hmatch z0 hz0S i).mp hi) (by rw [← hFz0]; exact hFvan z0 hz0S)
            (by rw [hf1z]; exact hf1z_ne) hWF_hi
            (fun h2 => by rw [hf0z, hf1z]; exact hresz (by rw [← hf1z]; exact h2))
            (by rw [hf0z, hf1z, hd0z, hd1z]; exact hT4)
        have hnop64 := List.all_eq_true.mp certsT1_no_p64 c hc_mem
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnop64
        have hpars : 1 ≤ c.s ∧ 0 < c.cHiDen ∧ 0 < c.δNum ∧ 0 < c.δDen := by
          unfold checkCapWitness at hcap1
          by_contra hbadp; push Not at hbadp
          have hif : (c.m == 0 || c.s < 1 || c.cHiDen == 0 || c.δNum == 0 || c.δDen == 0 || (1 : ℕ) == 0) = true := by
            rcases lt_or_ge c.s 1 with h1 | h1
            · simp [h1]
            · rcases Nat.eq_zero_or_pos c.cHiDen with h2 | h2
              · simp [h2]
              · rcases Nat.eq_zero_or_pos c.δNum with h3 | h3
                · simp [h3]
                · have h4 : c.δDen = 0 := by have := hbadp h1 h2 h3; omega
                  simp [h4]
          rw [if_pos hif] at hcap1; cases hcap1
        rcases hq₀ with rfl | rfl
        · simp only [↓reduceIte]
          have hcard1 := card_le_of_quotient_surplus u₀ u₁ c.cap1 hcap1 (Or.inl rfl) le_rfl hpars.1 hmpos
            hpars.2.1 hpars.2.2.1 hpars.2.2.2 (by omega) hWF_lo hcHi f_coord hirr hFdeg hFwdeg hf_wYZ k
            (fun i => ⟨(hk_exact i).1, (hk_exact i).2 c.m⟩) hsurp S_clean P Az
            (fun z hz => hP z (hS_clean_sub hz)) (fun z hz => hFvan z (hS_clean_sub hz))
            (fun z hz => hcard z (hS_clean_sub hz)) (fun z hz => hmatch z (hS_clean_sub hz))
            (fun z hz => hbad z (hS_clean_sub hz)) (fun h => by rw [hnop64.1] at h; cases h)
          have h1 : (c.cap1.c1Bkt : ℚ) ≤ (T4_C1_SUM : ℚ) := by exact_mod_cast hc1_le
          have h0 : (c.cap1.c0Bkt : ℚ) ≤ (T4_C0_SUM : ℚ) := by exact_mod_cast hc0_le
          have hmul := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℚ) D_ZF)
          linarith only [hcard1, hmul, h0]
        · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
          obtain ⟨hW13, hDZ3850⟩ := hq2_cond rfl
          obtain ⟨hcap2, hq2_le⟩ := hcap2_fn hW13
          have hcard2 := card_le_of_quotient_surplus u₀ u₁ c.cap2 hcap2 (Or.inr rfl) le_rfl hpars.1 hmpos
            hpars.2.1 hpars.2.2.1 hpars.2.2.2 (by omega) hWF_lo hcHi f_coord hirr hFdeg hFwdeg hf_wYZ k
            (fun i => ⟨(hk_exact i).1, (hk_exact i).2 c.m⟩) hsurp S_clean P Az
            (fun z hz => hP z (hS_clean_sub hz)) (fun z hz => hFvan z (hS_clean_sub hz))
            (fun z hz => hcard z (hS_clean_sub hz)) (fun z hz => hmatch z (hS_clean_sub hz))
            (fun z hz => hbad z (hS_clean_sub hz)) (fun h => by rw [hnop64.2] at h; cases h)
          have hq : (c.cap2.c1Bkt : ℚ) * (D_ZF : ℚ) + (c.cap2.c0Bkt : ℚ) ≤ (T4_Q2_SUM : ℚ) := by
            have hDZQ : (D_ZF : ℚ) ≤ 3850 := by exact_mod_cast hDZ3850
            have hle : (c.cap2.c1Bkt : ℚ) * 3850 + (c.cap2.c0Bkt : ℚ) ≤ (T4_Q2_SUM : ℚ) := by exact_mod_cast hq2_le
            have hmul := mul_le_mul_of_nonneg_left hDZQ (Nat.cast_nonneg (α := ℚ) c.cap2.c1Bkt)
            linarith only [hmul, hle]
          exact hcard2.trans hq
      · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty, Nat.cast_zero]
        split_ifs <;> positivity
    have htot : (S.card : ℚ) ≤ (S_clean.card : ℚ) + 52 * (D_ZF : ℚ) := by exact_mod_cast hS_split
    rcases hq₀ with rfl | rfl
    · simp only [↓reduceIte] at hcl ⊢; push_cast; linarith [Nat.cast_nonneg (α := ℚ) D_ZF]
    · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at hcl ⊢
      have hDZQ : (D_ZF : ℚ) ≤ 3850 := by exact_mod_cast (hq2_cond rfl).2
      push_cast; linarith

/-- **Unified `deg_R = 2, f_1 ≠ 0` Single-Factor Bound (Tables 2, 3, 2A, 2B, `q₀ = 1`):**
For ANY irreducible `ker(D)` factor `F ∈ K_{W_F}(2)[Z]` with `f_1 ≠ 0`, `W_F / wY ≤ 51 / 2`, `D_ZF ≤ 3850`:
`(S.card : ℚ) ≤ T3_CAP_BOUND + 8000000200200` (`≈ 18.308e18 < 18.4e18`)! -/
theorem deg2_factor_card_le
    (u₀ u₁ : Idx → Fld) {W_F D_ZF : ℕ}
    (hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2)
    (hDZ_le : D_ZF ≤ 3850)
    (f_coord : KerDIdx wY W_F 2 → Polynomial Fld)
    (hirr : Irreducible (liftCRat (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1)))
    (hFdeg : (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).natDegree = 2)
    (hf1_ne : (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1).coeff 1 ≠ 0)
    (hFwdeg : wdeg wY (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1) = W_F)
    (hf_wYZ : wYZ 1 (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1) ≤ D_ZF)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hFvan : ∀ z ∈ S, evalContact (evalZContact (∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1) z) (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6401 u₀ u₁ (Az z)) :
    (S.card : ℚ) ≤ ((T3_CAP_BOUND + 8000000200200 : ℕ) : ℚ) := by
  classical
  let Fpoly : ContactPoly (Polynomial Fld) := ∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1
  have hFne : Fpoly ≠ 0 := fun h0 => hirr.ne_zero (by change liftCRat Fpoly = 0; rw [h0, map_zero])
  have hf2_ne : Fpoly.coeff 2 ≠ 0 := by
    rw [← hFdeg, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hFne
  have hWF_lo : 2 * (wY - 1) ≤ W_F := by
    have h1 := wdegBiDom_coeff_le_of_wdeg (le_of_eq hFwdeg) 2 hf2_ne; omega
  have hZ_F : ∀ k' j' i', (((Fpoly.coeff k').coeff j').coeff i').natDegree ≤ D_ZF :=
    natDegree_Z_le_of_wYZ hf_wYZ
  let f0 := Fpoly.coeff 0
  let f1 := Fpoly.coeff 1
  let f2 := Fpoly.coeff 2
  have hWF_25 : 2 * W_F ≤ 51 * wY := by
    have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
    have := (div_le_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 2)).mp hWF_hi
    exact_mod_cast (show (2 : ℚ) * (W_F : ℚ) ≤ 51 * (wY : ℚ) by linarith)
  have hd0_le25 : f0.natDegree ≤ 25 := by
    by_cases h0 : f0 = 0
    · simp [h0]
    · have hw0 : wdegBiDom wY f0 ≤ W_F := by
        simpa only [Nat.zero_mul, Nat.sub_zero] using wdegBiDom_le_of_wdeg_coeff (le_of_eq hFwdeg) 0
      have h1 := wdegBiDom_ge_natDegree_mul wY f0 h0
      have hwY : wY = 1048575 := rfl
      rw [hwY] at hw0 h1 hWF_25; omega
  have hd1_le24 : f1.natDegree ≤ 24 := by
    have hw1 : wdegBiDom wY f1 + (wY - 1) ≤ W_F := by
      simpa only [one_mul] using wdegBiDom_coeff_le_of_wdeg (le_of_eq hFwdeg) 1 hf1_ne
    have h1 := wdegBiDom_ge_natDegree_mul wY f1 hf1_ne
    have hwY : wY = 1048575 := rfl
    rw [hwY] at hw1 h1 hWF_25; omega
  have hd2_le24 : f2.natDegree ≤ 24 := by
    have hw2 : wdegBiDom wY f2 + 2 * (wY - 1) ≤ W_F := wdegBiDom_coeff_le_of_wdeg (le_of_eq hFwdeg) 2 hf2_ne
    have h1 := wdegBiDom_ge_natDegree_mul wY f2 hf2_ne
    have hwY : wY = 1048575 := rfl
    rw [hwY] at hw2 h1 hWF_25; omega
  obtain ⟨hf0_ne, t, hht_ne, hres_ne⟩ := exists_t_resY_ne_zero_of_irred_deg2 Fpoly hirr hFdeg hf1_ne hf2_ne hd0_le25
  let ht : BiPoly (Polynomial Fld) := f1 + Polynomial.C (Polynomial.C (Polynomial.C t)) * f2
  have hht_deg : ht.natDegree ≤ 24 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le hd1_le24 ?_)
    exact (Polynomial.natDegree_C_mul_le _ _).trans hd2_le24
  have hht_degZ : ∀ j a, ((ht.coeff j).coeff a).natDegree ≤ D_ZF := by
    intro j a
    dsimp only [ht]
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (hZ_F 1 j a) ?_)
    exact (Polynomial.natDegree_C_mul_le _ _).trans (hZ_F 2 j a)
  let R : Polynomial (Polynomial Fld) := Polynomial.resultant f0 ht f0.natDegree ht.natDegree
  -- Peel off `f1(z, P z) = 0`, `f2(z, P z) = 0`, `f0_z deg drop`, `ht_z deg drop`, `R(z) = 0`!
  let S_f1 := S.filter fun z => triEval f1 z (P z) = 0
  let S_f2 := S.filter fun z => triEval f2 z (P z) = 0
  let S_d0 := S.filter fun z => ¬ (evalZBiPoly f0 z ≠ 0 ∧ (evalZBiPoly f0 z).natDegree = f0.natDegree)
  let S_dh := S.filter fun z => ¬ (evalZBiPoly ht z ≠ 0 ∧ (evalZBiPoly ht z).natDegree = ht.natDegree)
  let S_R := S.filter fun z => R.map (Polynomial.evalRingHom z) = 0
  let S_clean := S.filter fun z =>
    triEval f1 z (P z) ≠ 0 ∧ triEval f2 z (P z) ≠ 0 ∧
    (evalZBiPoly f0 z ≠ 0 ∧ (evalZBiPoly f0 z).natDegree = f0.natDegree) ∧
    (evalZBiPoly ht z ≠ 0 ∧ (evalZBiPoly ht z).natDegree = ht.natDegree) ∧
    R.map (Polynomial.evalRingHom z) ≠ 0
  have hmatch1 : ∀ z ∈ S, ∀ i ∈ Az z, (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ 1 * u₁ i := fun z hz i hi => by
    simpa only [pow_one] using (hmatch z hz i).mp hi
  have hSf1_card : (S_f1.card : ℚ) ≤ (4000000000000 : ℚ) :=
    (card_le_of_biPoly_pow u₀ u₁ 1 le_rfl f1 24 D_ZF hf1_ne hd1_le24 (fun j a => hZ_F 1 j a)
      S_f1 P Az (fun z hz => hP z (Finset.mem_filter.mp hz).1) (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hcard z (Finset.mem_filter.mp hz).1) (fun z hz => hmatch1 z (Finset.mem_filter.mp hz).1)
      (fun z hz => hbad z (Finset.mem_filter.mp hz).1)).trans (card_le_of_biPoly_pow_deg2_bound le_rfl hDZ_le)
  have hSf2_card : (S_f2.card : ℚ) ≤ (4000000000000 : ℚ) :=
    (card_le_of_biPoly_pow u₀ u₁ 1 le_rfl f2 24 D_ZF hf2_ne hd2_le24 (fun j a => hZ_F 2 j a)
      S_f2 P Az (fun z hz => hP z (Finset.mem_filter.mp hz).1) (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hcard z (Finset.mem_filter.mp hz).1) (fun z hz => hmatch1 z (Finset.mem_filter.mp hz).1)
      (fun z hz => hbad z (Finset.mem_filter.mp hz).1)).trans (card_le_of_biPoly_pow_deg2_bound le_rfl hDZ_le)
  have hSd0_card : S_d0.card ≤ D_ZF := card_evalZBiPoly_good_deg_le f0 hf0_ne (fun j a => hZ_F 0 j a) S
  have hSdh_card : S_dh.card ≤ D_ZF := card_evalZBiPoly_good_deg_le ht hht_ne hht_degZ S
  have hSR_card : S_R.card ≤ 49 * D_ZF :=
    (card_evalZ_poly_eq_zero_le R hres_ne
      (degZ_resultant_biPoly_le f0 ht f0.natDegree ht.natDegree D_ZF (fun j a => hZ_F 0 j a) hht_degZ) S).trans
      (Nat.mul_le_mul_right D_ZF (by omega))
  have hS_split : S.card ≤ S_clean.card + S_f1.card + S_f2.card + S_d0.card + S_dh.card + S_R.card := by
    have hsub : S ⊆ S_clean ∪ (S_f1 ∪ (S_f2 ∪ (S_d0 ∪ (S_dh ∪ S_R)))) := by
      intro z hz; simp only [Finset.mem_union, S_clean, S_f1, S_f2, S_d0, S_dh, S_R, Finset.mem_filter]
      by_cases h1 : triEval f1 z (P z) = 0
      · exact Or.inr (Or.inl ⟨hz, h1⟩)
      · by_cases h2 : triEval f2 z (P z) = 0
        · exact Or.inr (Or.inr (Or.inl ⟨hz, h2⟩))
        · by_cases h3 : evalZBiPoly f0 z ≠ 0 ∧ (evalZBiPoly f0 z).natDegree = f0.natDegree
          · by_cases h4 : evalZBiPoly ht z ≠ 0 ∧ (evalZBiPoly ht z).natDegree = ht.natDegree
            · by_cases h5 : R.map (Polynomial.evalRingHom z) = 0
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hz, h5⟩))))
              · exact Or.inl ⟨hz, h1, h2, h3, h4, h5⟩
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hz, h4⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hz, h3⟩)))
    have hle := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_left (Finset.card_union_le _ _) _)) _)) _)) _))
    omega
  -- Global exact local orders `k i`!
  let Loc (i : Idx) : LocalPoly (Polynomial Fld) :=
    ∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly (Polynomial.C (BinaryIRSProfile.domain i)) (linePow u₀ u₁ 1 i) e.1
  have hLoc_ne : ∀ i : Idx, Loc i ≠ 0 := fun i =>
    localShift_ne_zero (Polynomial.C (BinaryIRSProfile.domain i)) (linePow u₀ u₁ 1 i) f_coord hFne
  let k : Idx → ℕ := fun i => exactTwOrd (Loc i)
  have hk_exact : ∀ i : Idx, twOrdGE (Loc i) (k i) ∧ (∀ m, k i < m → ∃ p q, p + q = k i ∧ twCoeff (Loc i) p q ≠ 0) :=
    fun i => ⟨twOrdGE_exactTwOrd (hLoc_ne i), fun _ _ => exists_twCoeff_exactTwOrd (hLoc_ne i)⟩
  have hS_clean_card : (S_clean.card : ℚ) ≤ (T3_CAP_BOUND : ℚ) := by
    by_cases hemp : S_clean.Nonempty
    · obtain ⟨z0, hz0⟩ := hemp
      obtain ⟨hz0S, hf1P, hf2P, ⟨hf0z_ne, hd0z⟩, ⟨hhtz_ne, hdhz⟩, hRz_ne⟩ := Finset.mem_filter.mp hz0
      have hFz0 : evalZContact Fpoly z0 = ∑ e : KerDIdx wY W_F 2, cC ((f_coord e).eval z0) * kerDBasisPoly e.1 :=
        evalZContact_sum_kerD f_coord z0
      have hf0z : (∑ e : KerDIdx wY W_F 2, cC ((f_coord e).eval z0) * kerDBasisPoly e.1).coeff 0 = evalZBiPoly f0 z0 := by
        rw [← hFz0]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f0]
      have hf1z : (∑ e : KerDIdx wY W_F 2, cC ((f_coord e).eval z0) * kerDBasisPoly e.1).coeff 1 = evalZBiPoly f1 z0 := by
        rw [← hFz0]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f1]
      have hf2z : (∑ e : KerDIdx wY W_F 2, cC ((f_coord e).eval z0) * kerDBasisPoly e.1).coeff 2 = evalZBiPoly f2 z0 := by
        rw [← hFz0]; simp only [evalZContact, evalZBiPoly, Polynomial.coeff_map, Polynomial.coe_mapRingHom, f2]
      have hhtz_eq : evalZBiPoly ht z0 = evalZBiPoly f1 z0 + Polynomial.C (Polynomial.C t) * evalZBiPoly f2 z0 := by
        unfold evalZBiPoly ht; simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
      have hcop_all : ∀ p : Polynomial (RatFunc Fld),
          p ∣ (evalZBiPoly f0 z0).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
          p ∣ (evalZBiPoly f1 z0).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
          p ∣ (evalZBiPoly f2 z0).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
          IsUnit p := by
        intro p hp0 hp1 hp2
        let ι : Polynomial Fld →+* RatFunc Fld := algebraMap (Polynomial Fld) (RatFunc Fld)
        have hι : Function.Injective ι := IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
        have hp_ht : p ∣ (evalZBiPoly ht z0).map ι := by
          rw [hhtz_eq, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
          exact dvd_add hp1 (dvd_mul_of_dvd_right hp2 _)
        have hres_z : Polynomial.resultant (evalZBiPoly f0 z0) (evalZBiPoly ht z0)
            (evalZBiPoly f0 z0).natDegree (evalZBiPoly ht z0).natDegree ≠ 0 := by
          rw [hd0z, hdhz]
          have hm := Polynomial.resultant_map_map f0 ht f0.natDegree ht.natDegree
            (Polynomial.mapRingHom (Polynomial.evalRingHom z0))
          dsimp only [R] at hRz_ne
          rw [← Polynomial.coe_mapRingHom, ← hm] at hRz_ne
          exact hRz_ne
        have hres_rat : Polynomial.resultant ((evalZBiPoly f0 z0).map ι) ((evalZBiPoly ht z0).map ι)
            ((evalZBiPoly f0 z0).map ι).natDegree ((evalZBiPoly ht z0).map ι).natDegree ≠ 0 := by
          rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι,
            Polynomial.resultant_map_map]
          exact fun h0 => hres_z (hι (h0.trans (map_zero ι).symm))
        by_contra hnu
        apply hres_rat
        have hf0L_ne : (evalZBiPoly f0 z0).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hf0z_ne
        have hhtL_ne : (evalZBiPoly ht z0).map ι ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hhtz_ne
        have hp_ne : p ≠ 0 := fun h0 => hf0L_ne (zero_dvd_iff.mp (h0 ▸ hp0))
        have hp_pos : 0 < p.natDegree := Nat.pos_of_ne_zero fun h0 =>
          hnu (Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree hp_ne, h0]; rfl))
        rcases hp0 with ⟨a, ha⟩
        rcases hp_ht with ⟨b, hb⟩
        have ha_ne : a ≠ 0 := fun h0 => hf0L_ne (by rw [ha, h0, mul_zero])
        have hb_ne : b ≠ 0 := fun h0 => hhtL_ne (by rw [hb, h0, mul_zero])
        have hres_pp : Polynomial.resultant p p p.natDegree p.natDegree = 0 := by
          have h0 := resultant_add_mul_right_deg (0 : Polynomial (RatFunc Fld)) p 1 p.natDegree p.natDegree
            (by simp) (by simp) rfl
          rw [zero_add, one_mul] at h0; rw [h0]
          exact Matrix.det_eq_zero_of_column_eq_zero (Fin.natAdd p.natDegree ⟨0, hp_pos⟩)
            (fun _ => by simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]; split_ifs <;> simp)
        rw [ha, hb, Polynomial.natDegree_mul hp_ne ha_ne, Polynomial.natDegree_mul hp_ne hb_ne,
          Polynomial.resultant_mul_left p a (p * b) (p.natDegree + b.natDegree) (by rw [Polynomial.natDegree_mul hp_ne hb_ne]),
          Polynomial.resultant_mul_right p p b p.natDegree le_rfl, hres_pp, zero_mul, zero_mul]
      have hvan_z0 : ∀ i : Idx, twOrdGE (∑ e : KerDIdx wY W_F 2,
          locC ((f_coord e).eval z0) * kerDLocalPoly (BinaryIRSProfile.domain i) (u₀ i + z0 * u₁ i) e.1) (k i) := fun i => by
        have h1 := twOrdGE_evalZLocal_sum (BinaryIRSProfile.domain i) (linePow u₀ u₁ 1 i) f_coord z0 (hk_exact i).1
        simpa [eval_linePow] using h1
      have hf1z_ne : evalZBiPoly f1 z0 ≠ 0 := fun h0 => hf1P (by change (evalZBiPoly f1 z0).eval (P z0) = 0; rw [h0, Polynomial.eval_zero])
      have hf2z_ne : evalZBiPoly f2 z0 ≠ 0 := fun h0 => hf2P (by change (evalZBiPoly f2 z0).eval (P z0) = 0; rw [h0, Polynomial.eval_zero])
      obtain ⟨m, s, cHiN, cHiD, δN, δD, w, hm, _, hs, _, hcHiD, hδN, hδD, hcHi, hsurp, hcap, hcap_bd⟩ :=
        t23_surplus_of_point (fun e => (f_coord e).eval z0) (fun i => u₀ i + z0 * u₁ i) k
          hvan_z0 (P z0) (hP z0 hz0S) (Az z0) (hcard z0 hz0S) (fun i hi => (hmatch z0 hz0S i).mp hi)
          (by rw [hf1z]; exact hf1z_ne) (by rw [hf2z]; exact hf2z_ne)
          (by rw [hf1z]; exact hf1P) (by rw [hf2z]; exact hf2P)
          hWF_hi (by simpa only [hf0z, hf1z, hf2z] using hcop_all)
      have hnop64 : w.useP64 = false := checkCapWitness_d2_no_p64 hcap
      have hcard_cl := card_le_of_quotient_surplus u₀ u₁ w hcap (Or.inl rfl) (by omega) hs hm
        hcHiD hδN hδD (by omega) hWF_lo hcHi f_coord hirr hFdeg hFwdeg hf_wYZ k
        (fun i => ⟨(hk_exact i).1, (hk_exact i).2 m⟩) hsurp S_clean P Az
        (fun z hz => hP z (Finset.mem_filter.mp hz).1) (fun z hz => hFvan z (Finset.mem_filter.mp hz).1)
        (fun z hz => hcard z (Finset.mem_filter.mp hz).1)
        (fun z hz i => by simpa only [pow_one] using hmatch z (Finset.mem_filter.mp hz).1 i)
        (fun z hz => hbad z (Finset.mem_filter.mp hz).1) (fun h => by rw [hnop64] at h; cases h)
      have hDZQ : (D_ZF : ℚ) ≤ 3850 := by exact_mod_cast hDZ_le
      have hle : (w.c1Bkt : ℚ) * 3850 + (w.c0Bkt : ℚ) ≤ (T3_CAP_BOUND : ℚ) := by exact_mod_cast hcap_bd
      nlinarith [Nat.cast_nonneg (α := ℚ) w.c1Bkt]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty, Nat.cast_zero]; positivity
  have hsplitQ : (S.card : ℚ) ≤ (S_clean.card : ℚ) + (S_f1.card : ℚ) + (S_f2.card : ℚ) +
      (S_d0.card : ℚ) + (S_dh.card : ℚ) + (S_R.card : ℚ) := by exact_mod_cast hS_split
  have hd0Q : (S_d0.card : ℚ) ≤ 3850 := by exact_mod_cast (hSd0_card.trans hDZ_le)
  have hdhQ : (S_dh.card : ℚ) ≤ 3850 := by exact_mod_cast (hSdh_card.trans hDZ_le)
  have hRQ : (S_R.card : ℚ) ≤ 49 * 3850 := by exact_mod_cast (hSR_card.trans (Nat.mul_le_mul_left 49 hDZ_le))
  push_cast; linarith

/-! ### Part 4: `ScalarListBound 10000000` (`deg_Z = 0, dy = 0`) -/

/-- Lift `ContactPoly Fld` into `ContactPoly (Polynomial Fld)` with constant `Z`-coefficients. -/
noncomputable def cLiftZ (F0 : ContactPoly Fld) : ContactPoly (Polynomial Fld) :=
  F0.map (Polynomial.mapRingHom (Polynomial.mapRingHom Polynomial.C))

lemma evalZContact_cLiftZ (F0 : ContactPoly Fld) (z : Fld) :
    evalZContact (cLiftZ F0) z = F0 := by
  unfold evalZContact cLiftZ
  simp only [Polynomial.map_map]
  have hid : (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.evalRingHom z))).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom Polynomial.C)) = RingHom.id (BiPoly Fld) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext a; simp
      · simp
    · simp
  rw [hid, Polynomial.map_id]

lemma cLiftZ_sum_kerDBasisPoly {W_F d : ℕ} (f_coord : KerDIdx wY W_F d → Fld) :
    cLiftZ (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) =
      ∑ e : KerDIdx wY W_F d, cC (Polynomial.C (f_coord e)) * kerDBasisPoly e.1 := by
  unfold cLiftZ; rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl; intro e _
  rw [Polynomial.map_mul]
  congr 1
  · unfold cC; simp [Polynomial.map_C]
  · unfold kerDBasisPoly cR cY cX
    simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C, Polynomial.map_X]

lemma cLiftZ_wdeg {F0 : ContactPoly Fld} : wdeg wY (cLiftZ F0) = wdeg wY F0 := by
  have h1 : ∀ W, wdeg wY (cLiftZ F0) ≤ W ↔ wdeg wY F0 ≤ W := fun W => by
    rw [wdeg_le_iff, wdeg_le_iff]
    constructor <;> intro h k j i hnz
    · exact h k j i (by simpa [cLiftZ] using hnz)
    · exact h k j i (by simpa [cLiftZ] using hnz)
  exact le_antisymm ((h1 _).mpr le_rfl) ((h1 _).mp le_rfl)

lemma cLiftZ_natDegree (F0 : ContactPoly Fld) : (cLiftZ F0).natDegree = F0.natDegree := by
  unfold cLiftZ
  exact Polynomial.natDegree_map_eq_of_injective
    (Polynomial.map_injective _ (Polynomial.map_injective _ Polynomial.C_injective)) F0

/-- Extract the coefficient of `Z^t` from `P ∈ ContactPoly (Polynomial Fld)` as an element of `ContactPoly Fld`! -/
private noncomputable def zSlice (P : ContactPoly (Polynomial Fld)) (t : ℕ) : ContactPoly Fld :=
  ∑ k ∈ P.support, Polynomial.monomial k (∑ j ∈ (P.coeff k).support,
    Polynomial.monomial j (∑ i ∈ ((P.coeff k).coeff j).support,
      Polynomial.monomial i ((((P.coeff k).coeff j).coeff i).coeff t)))

private lemma coeff_zSlice (P : ContactPoly (Polynomial Fld)) (t k j i : ℕ) :
    (((zSlice P t).coeff k).coeff j).coeff i = ((((P.coeff k).coeff j).coeff i).coeff t) := by
  unfold zSlice
  rw [finset_sum_coeff]
  by_cases hk : k ∈ P.support
  · rw [Finset.sum_eq_single k]
    · rw [Polynomial.coeff_monomial_same, finset_sum_coeff]
      by_cases hj : j ∈ (P.coeff k).support
      · rw [Finset.sum_eq_single j]
        · rw [Polynomial.coeff_monomial_same, finset_sum_coeff]
          by_cases hi : i ∈ ((P.coeff k).coeff j).support
          · rw [Finset.sum_eq_single i]
            · rw [Polynomial.coeff_monomial_same]
            · intro i' _ hne; simp [Polynomial.coeff_monomial, hne]
            · intro h; exact absurd hi h
          · rw [Finset.sum_eq_zero]
            · have h0 : ((P.coeff k).coeff j).coeff i = 0 := not_not.mp (Polynomial.mem_support_iff.not.mp hi)
              simp [h0]
            · intro i' hi'; simp [Polynomial.coeff_monomial, show i' ≠ i from fun h => hi (h ▸ hi')]
        · intro j' _ hne; simp [Polynomial.coeff_monomial, hne]
        · intro h; exact absurd hj h
      · rw [Finset.sum_eq_zero]
        · have h0 : (P.coeff k).coeff j = 0 := not_not.mp (Polynomial.mem_support_iff.not.mp hj)
          simp [h0]
        · intro j' hj'; simp [Polynomial.coeff_monomial, show j' ≠ j from fun h => hj (h ▸ hj')]
    · intro k' _ hne; simp [Polynomial.coeff_monomial, hne]
    · intro h; exact absurd hk h
  · rw [Finset.sum_eq_zero]
    · have h0 : P.coeff k = 0 := not_not.mp (Polynomial.mem_support_iff.not.mp hk)
      simp [h0]
    · intro k' hk'; simp [Polynomial.coeff_monomial, show k' ≠ k from fun h => hk (h ▸ hk')]

private lemma zSlice_mul (P Q : ContactPoly (Polynomial Fld)) (t : ℕ) :
    zSlice (P * Q) t = ∑ x ∈ Finset.antidiagonal t, zSlice P x.1 * zSlice Q x.2 := by
  apply Polynomial.ext; intro k; apply Polynomial.ext; intro j; apply Polynomial.ext; intro i
  rw [coeff_zSlice, finset_sum_coeff, finset_sum_coeff, finset_sum_coeff]
  simp only [Polynomial.coeff_mul, finset_sum_coeff]
  simp only [coeff_zSlice]
  simp_rw [Finset.sum_comm (s := Finset.antidiagonal i) (t := Finset.antidiagonal t)]
  simp_rw [Finset.sum_comm (s := Finset.antidiagonal j) (t := Finset.antidiagonal t)]
  rw [Finset.sum_comm]

private lemma zSlice_cC_mul (d : Polynomial Fld) (F0 : ContactPoly Fld) (t : ℕ) :
    zSlice (cC d * cLiftZ F0) t = cC (d.coeff t) * F0 := by
  apply Polynomial.ext; intro k; apply Polynomial.ext; intro j; apply Polynomial.ext; intro i
  rw [coeff_zSlice]
  have h1 : (((cC d * cLiftZ F0).coeff k).coeff j).coeff i = d * (((F0.coeff k).coeff j).coeff i |> Polynomial.C) := by
    unfold cC cLiftZ; simp [Polynomial.coeff_C_mul]
  have h2 : (((cC (d.coeff t) * F0).coeff k).coeff j).coeff i = d.coeff t * ((F0.coeff k).coeff j).coeff i := by
    unfold cC; simp [Polynomial.coeff_C_mul]
  rw [h1, h2, Polynomial.coeff_mul_C]

private lemma zSlice_eq_zero_of_all (P : ContactPoly (Polynomial Fld)) (h : ∀ t, zSlice P t = 0) : P = 0 := by
  apply Polynomial.ext; intro k; apply Polynomial.ext; intro j; apply Polynomial.ext; intro i; apply Polynomial.ext; intro t
  rw [← coeff_zSlice, h t]; simp

/-- Lifting irreducibility from `ContactPoly Fld` to `ContactPoly (RatFunc Fld)` via minimal-`Z` primality! -/
theorem irreducible_liftCRat_cLiftZ {F0 : ContactPoly Fld} (hirr : Irreducible F0) :
    Irreducible (liftCRat (cLiftZ F0)) := by
  classical
  let alg : Polynomial Fld →+* RatFunc Fld := algebraMap (Polynomial Fld) (RatFunc Fld)
  have halg_inj : Function.Injective alg := IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
  have hlift_inj : Function.Injective (liftCRat (F := Fld)) :=
    Polynomial.map_injective _ (Polynomial.map_injective _ (Polynomial.map_injective _ halg_inj))
  have hF0_prime : Prime F0 := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  -- Helper: any element of `ContactPoly (RatFunc Fld)` has a nonzero `d : Polynomial Fld` clearing denominators!
  have hclear : ∀ R : ContactPoly (RatFunc Fld),
      ∃ (d : Polynomial Fld) (R' : ContactPoly (Polynomial Fld)), d ≠ 0 ∧ cC (alg d) * R = liftCRat R' := by
    intro R
    let coords : Finset (ℕ × ℕ × ℕ) :=
      R.support.biUnion fun k => (R.coeff k).support.biUnion fun j =>
        ((R.coeff k).coeff j).support.image fun i => (k, j, i)
    have hsurj : ∀ c : ℕ × ℕ × ℕ, ∃ (n d : Polynomial Fld), d ≠ 0 ∧
        alg d * (((R.coeff c.1).coeff c.2.1).coeff c.2.2) = alg n := fun c => by
      obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (Polynomial Fld)) (((R.coeff c.1).coeff c.2.1).coeff c.2.2)
      exact ⟨n, d, nonZeroDivisors.ne_zero d.2, by simpa [mul_comm] using hd⟩
    choose nC dC hdC_ne hndC using hsurj
    let d : Polynomial Fld := ∏ c ∈ coords, dC c
    have hd_ne : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hdC_ne c
    have hnum : ∀ k j i, ∃ p : Polynomial Fld, alg d * (((R.coeff k).coeff j).coeff i) = alg p := by
      intro k j i
      by_cases hnz : ((R.coeff k).coeff j).coeff i = 0
      · exact ⟨0, by simp [hnz]⟩
      · have hmem : (k, j, i) ∈ coords := by
          simp only [coords, Finset.mem_biUnion, Finset.mem_image, Polynomial.mem_support_iff, Prod.mk.injEq]
          exact ⟨k, fun h => hnz (by simp [h]), j, fun h => hnz (by simp [h]), i, hnz, rfl, rfl, rfl⟩
        refine ⟨(∏ c ∈ coords.erase (k, j, i), dC c) * nC (k, j, i), ?_⟩
        have hd_eq : d = (∏ c ∈ coords.erase (k, j, i), dC c) * dC (k, j, i) := by
          dsimp [d]; rw [← Finset.mul_prod_erase _ _ hmem, mul_comm]
        rw [hd_eq, map_mul, map_mul, mul_assoc, hndC (k, j, i)]
    choose pC hpC using hnum
    let R' : ContactPoly (Polynomial Fld) :=
      ∑ k ∈ R.support, Polynomial.monomial k (∑ j ∈ (R.coeff k).support,
        Polynomial.monomial j (∑ i ∈ ((R.coeff k).coeff j).support, Polynomial.monomial i (pC k j i)))
    refine ⟨d, R', hd_ne, ?_⟩
    apply Polynomial.ext; intro k; apply Polynomial.ext; intro j; apply Polynomial.ext; intro i
    have hL : (((cC (alg d) * R).coeff k).coeff j).coeff i = alg d * (((R.coeff k).coeff j).coeff i) := by
      unfold cC; simp [Polynomial.coeff_C_mul]
    rw [hL, hpC k j i]
    have hR : (((liftCRat R').coeff k).coeff j).coeff i = alg (((R'.coeff k).coeff j).coeff i) := by
      dsimp only [alg]; simp [liftCRat, liftBiRat]
    rw [hR]; congr 1
    dsimp only [R']; rw [finset_sum_coeff]
    by_cases hk : k ∈ R.support
    · rw [Finset.sum_eq_single k]
      · rw [Polynomial.coeff_monomial_same, finset_sum_coeff]
        by_cases hj : j ∈ (R.coeff k).support
        · rw [Finset.sum_eq_single j]
          · rw [Polynomial.coeff_monomial_same, finset_sum_coeff]
            by_cases hi : i ∈ ((R.coeff k).coeff j).support
            · rw [Finset.sum_eq_single i]
              · rw [Polynomial.coeff_monomial_same]
              · intro i' _ hne; simp [Polynomial.coeff_monomial, hne]
              · intro h; exact absurd hi h
            · rw [Finset.sum_eq_zero]
              · have h0 : ((R.coeff k).coeff j).coeff i = 0 := not_not.mp (Polynomial.mem_support_iff.not.mp hi)
                apply halg_inj; rw [← hpC, h0, mul_zero, map_zero]
              · intro i' hi'; simp [Polynomial.coeff_monomial, show i' ≠ i from fun h => hi (h ▸ hi')]
          · intro j' _ hne; simp [Polynomial.coeff_monomial, hne]
          · intro h; exact absurd hj h
        · rw [Finset.sum_eq_zero]
          · have h0 : (R.coeff k).coeff j = 0 := not_not.mp (Polynomial.mem_support_iff.not.mp hj)
            rw [Polynomial.coeff_zero]; apply halg_inj; rw [← hpC, h0, Polynomial.coeff_zero, mul_zero, map_zero]
          · intro j' hj'; simp [Polynomial.coeff_monomial, show j' ≠ j from fun h => hj (h ▸ hj')]
      · intro k' _ hne; simp [Polynomial.coeff_monomial, hne]
      · intro h; exact absurd hk h
    · rw [Finset.sum_eq_zero]
      · have h0 : R.coeff k = 0 := not_not.mp (Polynomial.mem_support_iff.not.mp hk)
        rw [Polynomial.coeff_zero, Polynomial.coeff_zero]
        apply halg_inj; rw [← hpC, h0, Polynomial.coeff_zero, Polynomial.coeff_zero, mul_zero, map_zero]
      · intro k' hk'; simp [Polynomial.coeff_monomial, show k' ≠ k from fun h => hk (h ▸ hk')]
  -- Minimal-`Z` primality: if `F0 ∣ zSlice (A * B) t` for all `t`, then `(∀ t, F0 ∣ zSlice A t) ∨ (∀ t, F0 ∣ zSlice B t)`!
  have hprime_slice : ∀ (A B : ContactPoly (Polynomial Fld)),
      (∀ t, F0 ∣ zSlice (A * B) t) → (∀ t, F0 ∣ zSlice A t) ∨ (∀ t, F0 ∣ zSlice B t) := by
    intro A B hAB
    by_contra hnot; push Not at hnot
    obtain ⟨hAex, hBex⟩ := hnot
    let tA := Nat.find hAex
    let tB := Nat.find hBex
    have htA : ¬ F0 ∣ zSlice A tA := Nat.find_spec hAex
    have htB : ¬ F0 ∣ zSlice B tB := Nat.find_spec hBex
    have hAB_t := hAB (tA + tB)
    rw [zSlice_mul, ← Finset.add_sum_erase _ _ (a := (tA, tB)) (Finset.mem_antidiagonal.mpr rfl)] at hAB_t
    have hrest_dvd : F0 ∣ ∑ x ∈ (Finset.antidiagonal (tA + tB)).erase (tA, tB), zSlice A x.1 * zSlice B x.2 := by
      apply Finset.dvd_sum; intro x hx
      have hne := (Finset.mem_erase.mp hx).1
      have hsum := Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hx).2
      rcases lt_or_gt_of_ne (show x.1 ≠ tA by intro h; apply hne; exact Prod.ext h (by omega)) with hlt | hgt
      · have hAd : F0 ∣ zSlice A x.1 := by by_contra hn; exact Nat.find_min hAex hlt hn
        rcases hAd with ⟨q, hq⟩
        exact ⟨q * zSlice B x.2, by rw [hq]; ring⟩
      · have hBd : F0 ∣ zSlice B x.2 := by by_contra hn; exact Nat.find_min hBex (show x.2 < tB by omega) hn
        rcases hBd with ⟨q, hq⟩
        exact ⟨zSlice A x.1 * q, by rw [hq]; ring⟩
    have hprod_dvd : F0 ∣ zSlice A tA * zSlice B tB := by
      rcases hAB_t with ⟨q1, hq1⟩
      rcases hrest_dvd with ⟨q2, hq2⟩
      exact ⟨q1 - q2, by linear_combination hq1 - hq2⟩
    rcases hF0_prime.dvd_or_dvd hprod_dvd with h | h
    · exact htA h
    · exact htB h
  -- Reconstruct `cLiftZ F0 ∣ P` from `∀ t, F0 ∣ zSlice P t`!
  have hdvd_of_slice : ∀ P : ContactPoly (Polynomial Fld), (∀ t, F0 ∣ zSlice P t) → cLiftZ F0 ∣ P := by
    intro P hP
    choose q hq using hP
    let T := P.support.sup fun k => (P.coeff k).support.sup fun j =>
      ((P.coeff k).coeff j).support.sup fun i => (((P.coeff k).coeff j).coeff i).natDegree
    have hP_zero : ∀ t, T < t → zSlice P t = 0 := fun t ht => by
      apply Polynomial.ext; intro k; apply Polynomial.ext; intro j; apply Polynomial.ext; intro i
      rw [coeff_zSlice]; simp only [Polynomial.coeff_zero]
      by_cases hnz : ((P.coeff k).coeff j).coeff i = 0
      · simp [hnz]
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hk : k ∈ P.support := Polynomial.mem_support_iff.mpr fun h => hnz (by simp [h])
        have hj : j ∈ (P.coeff k).support := Polynomial.mem_support_iff.mpr fun h => hnz (by simp [h])
        have hi : i ∈ ((P.coeff k).coeff j).support := Polynomial.mem_support_iff.mpr hnz
        have hle1 : (((P.coeff k).coeff j).coeff i).natDegree ≤ T :=
          (Finset.le_sup (f := fun i' => (((P.coeff k).coeff j).coeff i').natDegree) hi).trans
            ((Finset.le_sup (f := fun j' => ((P.coeff k).coeff j').support.sup fun i' => (((P.coeff k).coeff j').coeff i').natDegree) hj).trans
              (Finset.le_sup (f := fun k' => (P.coeff k').support.sup fun j' => ((P.coeff k').coeff j').support.sup fun i' => (((P.coeff k').coeff j').coeff i').natDegree) hk))
        omega
    let Q : ContactPoly (Polynomial Fld) := ∑ t ∈ Finset.range (T + 1), cC (Polynomial.X ^ t) * cLiftZ (q t)
    refine ⟨Q, ?_⟩
    have hmul_sum : cLiftZ F0 * Q = ∑ t ∈ Finset.range (T + 1), cC (Polynomial.X ^ t) * cLiftZ (F0 * q t) := by
      dsimp only [Q]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _
      have hc : cLiftZ (F0 * q t) = cLiftZ F0 * cLiftZ (q t) := by unfold cLiftZ; simp [Polynomial.map_mul]
      rw [hc]; ring
    rw [hmul_sum]
    apply Polynomial.ext; intro k; apply Polynomial.ext; intro j; apply Polynomial.ext; intro i; apply Polynomial.ext; intro t
    rw [← coeff_zSlice, finset_sum_coeff, finset_sum_coeff, finset_sum_coeff, finset_sum_coeff]
    have hterm : ∀ t' : ℕ,
        ((((cC (Polynomial.X ^ t') * cLiftZ (F0 * q t')).coeff k).coeff j).coeff i).coeff t =
          if t' = t then (((F0 * q t').coeff k).coeff j).coeff i else 0 := fun t' => by
      rw [← coeff_zSlice, zSlice_cC_mul, Polynomial.coeff_X_pow]
      split_ifs <;> simp_all [cC, Polynomial.coeff_C_mul]
    simp_rw [hterm]
    by_cases ht : t < T + 1
    · rw [Finset.sum_eq_single t]
      · simp [hq t]
      · intro t' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_range.mpr ht) h
    · rw [Finset.sum_eq_zero]
      · rw [hP_zero t (by omega)]; simp
      · intro t' ht'; have := Finset.mem_range.mp ht'; simp [show t' ≠ t by omega]
  refine ⟨?_, ?_⟩
  · intro hu
    -- A unit in `ContactPoly (RatFunc Fld)` has `natDegree = 0` in `R`, `Y`, `X`, contradicting `hirr.not_isUnit`!
    have hR0 : (liftCRat (cLiftZ F0)).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hF0_R0 : F0.natDegree = 0 := by
      have hmap_inj : Function.Injective (Polynomial.mapRingHom (Polynomial.mapRingHom alg)) :=
        Polynomial.map_injective _ (Polynomial.map_injective _ halg_inj)
      have h1 : (liftCRat (cLiftZ F0)).natDegree = (cLiftZ F0).natDegree :=
        Polynomial.natDegree_map_eq_of_injective hmap_inj (cLiftZ F0)
      rw [cLiftZ_natDegree] at h1; omega
    have hC1 := Polynomial.eq_C_of_natDegree_eq_zero hF0_R0
    have hu1 : IsUnit (liftBiRat ((cLiftZ F0).coeff 0)) := by
      rcases hu with ⟨u, hu⟩
      have h0 := congrArg (fun p : ContactPoly (RatFunc Fld) => p.coeff 0) u.mul_inv
      rw [hu, liftCRat, Polynomial.mul_coeff_zero, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_one_zero] at h0
      exact isUnit_iff_exists_inv.mpr ⟨_, h0⟩
    have hY0 : (F0.coeff 0).natDegree = 0 := by
      have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu1
      have h2 : (liftBiRat ((cLiftZ F0).coeff 0)).natDegree = (F0.coeff 0).natDegree := by
        unfold liftBiRat cLiftZ; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
        rw [Polynomial.natDegree_map_eq_of_injective (Polynomial.map_injective _ halg_inj),
            Polynomial.natDegree_map_eq_of_injective (Polynomial.map_injective _ Polynomial.C_injective)]
      omega
    let φ : Fld →+* RatFunc Fld := alg.comp Polynomial.C
    have hφ : Function.Injective φ := halg_inj.comp Polynomial.C_injective
    have hu2 : IsUnit (((F0.coeff 0).coeff 0).map φ) := by
      rcases hu1 with ⟨u, hu⟩
      have h0 := congrArg (fun p : BiPoly (RatFunc Fld) => p.coeff 0) u.mul_inv
      rw [hu, Polynomial.mul_coeff_zero, Polynomial.coeff_one_zero] at h0
      have heq : (liftBiRat ((cLiftZ F0).coeff 0)).coeff 0 = ((F0.coeff 0).coeff 0).map φ := by
        unfold liftBiRat cLiftZ φ alg; simp [Polynomial.map_map]
      rw [heq] at h0; exact isUnit_iff_exists_inv.mpr ⟨_, h0⟩
    have hX0 : ((F0.coeff 0).coeff 0).natDegree = 0 := by
      have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu2
      have h2 : (((F0.coeff 0).coeff 0).map φ).natDegree = ((F0.coeff 0).coeff 0).natDegree :=
        Polynomial.natDegree_map_eq_of_injective hφ ((F0.coeff 0).coeff 0)
      omega
    have hne : (((F0.coeff 0).coeff 0).coeff 0) ≠ 0 := by
      intro h0; apply hirr.ne_zero
      rw [hC1, Polynomial.eq_C_of_natDegree_eq_zero hY0, Polynomial.eq_C_of_natDegree_eq_zero hX0, h0]
      simp
    apply hirr.not_isUnit
    rw [hC1, Polynomial.eq_C_of_natDegree_eq_zero hY0, Polynomial.eq_C_of_natDegree_eq_zero hX0]
    exact Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hne)))
  · intro a b hab
    obtain ⟨da, A, hda, hA⟩ := hclear a
    obtain ⟨db, B, hdb, hB⟩ := hclear b
    have hprod_rat : liftCRat (cC (da * db) * cLiftZ F0) = liftCRat (A * B) := by
      rw [map_mul, map_mul, ← hA, ← hB, show liftCRat (cC (da * db)) = cC (alg da) * cC (alg db) by
        dsimp only [alg]; unfold liftCRat liftBiRat cC; simp [map_mul, Polynomial.map_C]]
      rw [hab]; ring
    have hprod : cC (da * db) * cLiftZ F0 = A * B := hlift_inj hprod_rat
    have hAB_slice : ∀ t, F0 ∣ zSlice (A * B) t := fun t => by
      rw [← hprod, zSlice_cC_mul]; exact dvd_mul_left F0 _
    have hunit_of_dvd : ∀ (d1 : Polynomial Fld) (X1 Y1 : ContactPoly (Polynomial Fld)) (y1 : ContactPoly (RatFunc Fld)),
        d1 ≠ 0 → cC (alg d1) * y1 = liftCRat Y1 → cC (da * db) * cLiftZ F0 = X1 * Y1 → cLiftZ F0 ∣ X1 →
        IsUnit y1 := by
      intro d1 X1 Y1 y1 hd1 hy1 heq ⟨U, hU⟩
      rw [hU] at heq
      have hF_ne : cLiftZ F0 ≠ 0 := fun h0 => hirr.ne_zero (by rw [← evalZContact_cLiftZ F0 0, h0]; rfl)
      have hcancel : cC (da * db) = U * Y1 := mul_left_cancel₀ hF_ne (by
        calc cLiftZ F0 * cC (da * db) = cC (da * db) * cLiftZ F0 := by ring
          _ = cLiftZ F0 * U * Y1 := heq
          _ = cLiftZ F0 * (U * Y1) := by ring)
      have hlift_c := congrArg liftCRat hcancel
      rw [map_mul, ← hy1] at hlift_c
      have hc_eq : liftCRat (cC (da * db)) = cC (alg (da * db)) := by
        dsimp only [alg]; unfold liftCRat liftBiRat cC; simp [Polynomial.map_C]
      rw [hc_eq] at hlift_c
      have hu_d : IsUnit (cC (alg (da * db)) : ContactPoly (RatFunc Fld)) := by
        have hne : alg (da * db) ≠ 0 := fun h0 => mul_ne_zero hda hdb (halg_inj (h0.trans (map_zero alg).symm))
        exact Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hne)))
      rcases hu_d with ⟨u, hu⟩
      exact isUnit_iff_exists_inv.mpr ⟨liftCRat U * cC (alg d1) * u.inv, by
        calc y1 * (liftCRat U * cC (alg d1) * u.inv)
            = (liftCRat U * (cC (alg d1) * y1)) * u.inv := by ring
          _ = cC (alg (da * db)) * u.inv := by rw [← hlift_c]
          _ = (u : ContactPoly (RatFunc Fld)) * u.inv := by rw [hu]
          _ = 1 := u.mul_inv⟩
    rcases hprime_slice A B hAB_slice with hA_sl | hB_sl
    · right; exact hunit_of_dvd db A B b hdb hB hprod (hdvd_of_slice A hA_sl)
    · left; exact hunit_of_dvd da B A a hda hA (by rw [hprod]; ring) (hdvd_of_slice B hB_sl)

/-- Over finite char-2 field `Fld`, NO irreducible `F0 ∈ ker(D)` of `deg_R = 2` can have `F0.coeff 1 = 0`! -/
lemma not_irred_kerD2_coeff1_zero {F0 : ContactPoly Fld}
    (hirr : Irreducible F0) (hD : contactDeriv F0 = 0) (hdeg : F0.natDegree = 2) (hf1 : F0.coeff 1 = 0) :
    False := by
  classical
  have ⟨hf2_d, _, _, _, hf0_d, _⟩ := kerD2_pde_facts hD (le_of_eq hdeg)
  have hf0_evY : ∀ j, j % 2 = 1 → (F0.coeff 0).coeff j = 0 :=
    (deriv_eq_zero_iff_even_coeffs (F0.coeff 0)).mp (by rw [hf0_d, hf1, dXBi_zero])
  have hf2_evY : ∀ j, j % 2 = 1 → (F0.coeff 2).coeff j = 0 :=
    (deriv_eq_zero_iff_even_coeffs (F0.coeff 2)).mp hf2_d
  have hX_ev : ∀ k j i, i % 2 = 1 → (((F0.coeff k).coeff j).coeff i) = 0 := by
    intro k j i hi
    have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
    rcases hk with rfl | rfl | rfl | hk3
    · have h0 := congrArg (fun Q : ContactPoly Fld => ((Q.coeff 0).coeff j).coeff (i - 1)) hD
      rw [coeff_contactDeriv, Polynomial.coeff_zero, Polynomial.coeff_zero, Polynomial.coeff_zero] at h0
      simp only [↓reduceIte, add_zero, coeff_dXBi, Polynomial.coeff_derivative] at h0
      have hi1 : i - 1 + 1 = i := by omega
      have hcast : ((i - 1 : ℕ) : Fld) + 1 = 1 := by
        have hev : (i - 1) % 2 = 0 := by omega
        have h2 : (2 : Fld) = 0 := CharTwo.two_eq_zero
        have : ((i - 1 : ℕ) : Fld) = 0 := by
          rw [show i - 1 = 2 * ((i - 1) / 2) by omega]; push_cast; rw [h2, zero_mul]
        rw [this, zero_add]
      rw [hi1, hcast, mul_one] at h0; exact h0
    · rw [hf1]; simp
    · have h2d := congrArg (fun Q : ContactPoly Fld => ((Q.coeff 2).coeff j).coeff (i - 1)) hD
      simp only [coeff_contactDeriv, show (2 : ℕ) ≠ 0 by decide, ↓reduceIte, show (2 : ℕ) - 1 = 1 by rfl,
        hf1, Polynomial.derivative_zero, add_zero, Polynomial.coeff_zero, coeff_dXBi,
        Polynomial.coeff_derivative] at h2d
      have hi1 : i - 1 + 1 = i := by omega
      have hcast : ((i - 1 : ℕ) : Fld) + 1 = 1 := by
        have h2 : (2 : Fld) = 0 := CharTwo.two_eq_zero
        have : ((i - 1 : ℕ) : Fld) = 0 := by
          rw [show i - 1 = 2 * ((i - 1) / 2) by omega]; push_cast; rw [h2, zero_mul]
        rw [this, zero_add]
      rw [hi1, hcast, mul_one] at h2d; exact h2d
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := F0) (by omega), Polynomial.coeff_zero, Polynomial.coeff_zero]
  have hY_ev : ∀ k j, j % 2 = 1 → (F0.coeff k).coeff j = 0 := by
    intro k j hj
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk3
    · exact hf0_evY j hj
    · rw [hf1]; simp
    · exact hf2_evY j hj
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := F0) (by omega), Polynomial.coeff_zero]
  -- Finite field char 2 Frobenius `x ↦ x ^ 2` is surjective!
  have hfrob_surj : Function.Surjective (frobenius Fld 2) :=
    Finite.surjective_of_injective (frobenius_inj Fld 2)
  let sqrtF (a : Fld) : Fld := Classical.choose (hfrob_surj a)
  have hsqrtF : ∀ a : Fld, (sqrtF a) ^ 2 = a := fun a => Classical.choose_spec (hfrob_surj a)
  have hsqrt0 : sqrtF 0 = 0 := by
    have h := hsqrtF 0
    exact (sq_eq_zero_iff).mp h
  let mkBi (g : BiPoly Fld) : BiPoly Fld :=
    ∑ j ∈ Finset.range (g.natDegree / 2 + 1), Polynomial.monomial j
      (∑ i ∈ Finset.range ((g.coeff (2 * j)).natDegree / 2 + 1),
        Polynomial.monomial i (sqrtF ((g.coeff (2 * j)).coeff (2 * i))))
  have hmkBi_sq : ∀ g : BiPoly Fld,
      (∀ j, j % 2 = 1 → g.coeff j = 0) → (∀ j i, i % 2 = 1 → (g.coeff j).coeff i = 0) →
      (mkBi g) ^ 2 = g := by
    intro g hgY hgX
    dsimp only [mkBi]
    rw [sum_pow_char 2]
    apply Polynomial.ext; intro j; apply Polynomial.ext; intro i
    rw [finset_sum_coeff, finset_sum_coeff]
    by_cases hj : j % 2 = 0
    · by_cases hj_le : j / 2 < g.natDegree / 2 + 1
      · rw [Finset.sum_eq_single (j / 2)]
        · rw [sq, Polynomial.monomial_mul_monomial, ← sq, sum_pow_char 2, show j / 2 + j / 2 = j by omega,
            Polynomial.coeff_monomial_same, finset_sum_coeff, show 2 * (j / 2) = j by omega]
          by_cases hi : i % 2 = 0
          · by_cases hi_le : i / 2 < (g.coeff j).natDegree / 2 + 1
            · rw [Finset.sum_eq_single (i / 2)]
              · rw [sq, Polynomial.monomial_mul_monomial, ← sq, hsqrtF, show i / 2 + i / 2 = i by omega,
                  show 2 * (i / 2) = i by omega, Polynomial.coeff_monomial_same]
              · intro i' _ hne
                rw [sq, Polynomial.monomial_mul_monomial]
                simp only [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg (show i' + i' ≠ i by omega)]
              · intro h; exact absurd (Finset.mem_range.mpr hi_le) h
            · rw [Finset.sum_eq_zero]
              · symm; exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
              · intro i' hi'; rw [sq, Polynomial.monomial_mul_monomial]
                simp only [Polynomial.coeff_monomial, Finsupp.single_apply,
                  if_neg (show i' + i' ≠ i by have := Finset.mem_range.mp hi'; omega)]
          · rw [Finset.sum_eq_zero, hgX j i (by omega)]
            intro i' _; rw [sq, Polynomial.monomial_mul_monomial]
            simp only [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg (show i' + i' ≠ i by omega)]
        · intro j' _ hne
          rw [sq, Polynomial.monomial_mul_monomial]
          simp only [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg (show j' + j' ≠ j by omega), Polynomial.coeff_zero]
        · intro h; exact absurd (Finset.mem_range.mpr hj_le) h
      · rw [Finset.sum_eq_zero]
        · symm; rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := g) (by omega), Polynomial.coeff_zero]
        · intro j' hj'; rw [sq, Polynomial.monomial_mul_monomial]
          simp only [Polynomial.coeff_monomial, Finsupp.single_apply,
            if_neg (show j' + j' ≠ j by have := Finset.mem_range.mp hj'; omega), Polynomial.coeff_zero]
    · rw [Finset.sum_eq_zero, hgY j (by omega), Polynomial.coeff_zero]
      intro j' _; rw [sq, Polynomial.monomial_mul_monomial]
      simp only [Polynomial.coeff_monomial, Finsupp.single_apply, if_neg (show j' + j' ≠ j by omega), Polynomial.coeff_zero]
  let H0 : ContactPoly Fld := Polynomial.C (mkBi (F0.coeff 0)) + Polynomial.C (mkBi (F0.coeff 2)) * Polynomial.X
  have hH0_sq : H0 ^ 2 = F0 := by
    have h2C : (2 : ContactPoly Fld) = 0 := CharTwo.two_eq_zero
    have hsq : H0 ^ 2 = Polynomial.C ((mkBi (F0.coeff 0)) ^ 2) + Polynomial.C ((mkBi (F0.coeff 2)) ^ 2) * Polynomial.X ^ 2 := by
      dsimp only [H0]; rw [map_pow, map_pow]
      linear_combination (Polynomial.C (mkBi (F0.coeff 0)) * Polynomial.C (mkBi (F0.coeff 2)) * Polynomial.X) * h2C
    rw [hsq, hmkBi_sq (F0.coeff 0) (hY_ev 0) (hX_ev 0), hmkBi_sq (F0.coeff 2) (hY_ev 2) (hX_ev 2)]
    apply Polynomial.ext; intro k
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk3
    · simp [Polynomial.coeff_C_mul_X_pow]
    · simp [hf1, Polynomial.coeff_C_mul_X_pow]
    · simp [Polynomial.coeff_C_mul_X_pow]
    · rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add,
        Polynomial.coeff_C_mul_X_pow, if_neg (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (p := F0) (by omega)]
  have hH0_deg : H0.natDegree = 1 := by
    have hH0_ne : H0 ≠ 0 := fun h0 => hirr.ne_zero (by rw [← hH0_sq, h0, zero_pow (by norm_num)])
    have h1 := Polynomial.natDegree_mul hH0_ne hH0_ne
    rw [← sq, hH0_sq, hdeg] at h1; omega
  rcases hirr.isUnit_or_isUnit (by rw [← hH0_sq, sq] : F0 = H0 * H0) with hu | hu <;>
    exact absurd (Polynomial.natDegree_eq_zero_of_isUnit hu) (by omega)

/-- Number of polynomial roots `P ∈ Fld[X]` of any nonzero `g ∈ BiPoly Fld` is at most `g.natDegree`! -/
lemma card_roots_biPoly_le {g : BiPoly Fld} (hg : g ≠ 0) (T : Finset (Polynomial Fld))
    (hT : ∀ P ∈ T, g.eval P = 0) : T.card ≤ g.natDegree := by
  classical
  let ι : Polynomial Fld →+* RatFunc Fld := algebraMap (Polynomial Fld) (RatFunc Fld)
  have hι : Function.Injective ι := IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
  let gR : Polynomial (RatFunc Fld) := g.map ι
  have hgR_ne : gR ≠ 0 := (Polynomial.map_ne_zero_iff hι).mpr hg
  have hsub : T.image ι ⊆ gR.roots.toFinset := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨P, hPT, rfl⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hgR_ne, Polynomial.IsRoot.def]
    rw [Polynomial.eval_map_apply, hT P hPT, map_zero]
  calc T.card = (T.image ι).card := (Finset.card_image_of_injective T hι).symm
    _ ≤ gR.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ gR.roots.card := Multiset.toFinset_card_le _
    _ ≤ gR.natDegree := Polynomial.card_roots' gR
    _ = g.natDegree := Polynomial.natDegree_map_eq_of_injective hι g

/-- `Resultant_R(F0, contactDeriv F0) ≠ 0` and has `deg_Y ≤ 125` whenever `F0` is irreducible
with `1 ≤ F0.natDegree ≤ 2`, `wdeg wY F0 ≤ 2 * A * 9 - 1`, and `contactDeriv F0 ≠ 0`. -/
private lemma card_roots_contactDeriv_le {F0 : ContactPoly Fld}
    (hirr : Irreducible F0) (hdeg1 : 1 ≤ F0.natDegree) (hdeg2 : F0.natDegree ≤ 2)
    (hW : wdeg wY F0 ≤ 2 * A * 9 - 1) (hDne : contactDeriv F0 ≠ 0)
    (TF : Finset (Polynomial Fld)) (hTF : ∀ P ∈ TF, evalContact F0 P = 0) :
    TF.card ≤ 150 := by
  classical
  have hwY1 : 1 ≤ wY := by norm_num [wY]
  have hndvd : ¬ F0 ∣ contactDeriv F0 := by
    rw [dvd_contactDeriv_iff wY hwY1 hirr.ne_zero]; exact hDne
  let dF := F0.natDegree
  let dD := (contactDeriv F0).natDegree
  have hdD_le : dD ≤ dF + 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro k hk
    have hk1 : F0.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hk2 : F0.coeff (k - 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [coeff_contactDeriv, show k ≠ 0 by omega, ↓reduceIte, hk1, hk2, dXBi_zero, Polynomial.derivative_zero, add_zero]
  let R_el : BiPoly Fld := Polynomial.resultant F0 (contactDeriv F0) dF dD
  have hRel_ne : R_el ≠ 0 := by
    have hprim : F0.IsPrimitive := hirr.isPrimitive (by omega)
    let ι : BiPoly Fld →+* FractionRing (BiPoly Fld) := algebraMap (BiPoly Fld) (FractionRing (BiPoly Fld))
    have hι : Function.Injective ι := IsFractionRing.injective (BiPoly Fld) (FractionRing (BiPoly Fld))
    have hirrK : Irreducible (F0.map ι) := hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
    have hndvdK : ¬ F0.map ι ∣ (contactDeriv F0).map ι := fun h =>
      hndvd (hprim.dvd_of_fraction_map_dvd_fraction_map h)
    have hcop : IsCoprime (F0.map ι) ((contactDeriv F0).map ι) := by
      refine EuclideanDomain.isCoprime_of_dvd (x := F0.map ι) (y := (contactDeriv F0).map ι) (fun h => hirrK.ne_zero h.1) ?_
      intro p hp _ hpF hpD
      rcases hpF with ⟨q, hq⟩
      rcases hirrK.isUnit_or_isUnit hq with hu | hqu
      · exact hp hu
      · rcases hqu with ⟨u, hu⟩
        have hdvd_p : F0.map ι ∣ p := ⟨(u⁻¹ : _), by rw [hq, ← hu, mul_assoc, Units.mul_inv, mul_one]⟩
        exact hndvdK (hdvd_p.trans hpD)
    intro h0
    have hresK : Polynomial.resultant (F0.map ι) ((contactDeriv F0).map ι)
        (F0.map ι).natDegree ((contactDeriv F0).map ι).natDegree = 0 := by
      rw [Polynomial.natDegree_map_eq_of_injective hι, Polynomial.natDegree_map_eq_of_injective hι,
        Polynomial.resultant_map_map, show Polynomial.resultant F0 (contactDeriv F0) dF dD = 0 from h0, map_zero]
    exact Polynomial.resultant_ne_zero _ _ hcop hresK
  have hRel_eval : ∀ P ∈ TF, R_el.eval P = 0 := by
    intro P hP
    have hFP : evalContact F0 P = 0 := hTF P hP
    have hDP : evalContact (contactDeriv F0) P = 0 := by
      rw [evalContact_contactDeriv, hFP, Polynomial.derivative_zero]
    let ψ : BiPoly Fld →+* RatFunc Fld := (algebraMap (Polynomial Fld) (RatFunc Fld)).comp (Polynomial.evalRingHom P)
    have hψ_inj : Function.Injective (algebraMap (Polynomial Fld) (RatFunc Fld)) :=
      IsFractionRing.injective (Polynomial Fld) (RatFunc Fld)
    apply hψ_inj; rw [map_zero]
    change ψ R_el = 0
    rw [show ψ R_el = Polynomial.resultant (F0.map ψ) ((contactDeriv F0).map ψ) dF dD from
      (Polynomial.resultant_map_map F0 (contactDeriv F0) dF dD ψ).symm]
    refine P64Resultant.fixed_resultant_eq_zero_of_common_root
      (y := algebraMap (Polynomial Fld) (RatFunc Fld) P.derivative)
      (Polynomial.natDegree_map_le) (Polynomial.natDegree_map_le) (by omega) ?_ ?_
    · have hcomm : (F0.map ψ).eval (algebraMap (Polynomial Fld) (RatFunc Fld) P.derivative) =
          algebraMap (Polynomial Fld) (RatFunc Fld) (evalContact F0 P) := by
        unfold evalContact ψ
        rw [← Polynomial.map_map, Polynomial.eval_map_apply]
      simpa [hFP] using hcomm
    · have hcomm : ((contactDeriv F0).map ψ).eval (algebraMap (Polynomial Fld) (RatFunc Fld) P.derivative) =
          algebraMap (Polynomial Fld) (RatFunc Fld) (evalContact (contactDeriv F0) P) := by
        unfold evalContact ψ
        rw [← Polynomial.map_map, Polynomial.eval_map_apply]
      simpa [hDP] using hcomm
  have hRel_deg : R_el.natDegree ≤ 150 := by
    have hW_D : wdeg wY (contactDeriv F0) ≤ 2 * A * 9 - 1 := by
      have h1 := wdeg_contactDeriv_add_one_le wY hwY1 F0 hDne; omega
    have hdeg_coeff : ∀ (Q : ContactPoly Fld), wdeg wY Q ≤ 2 * A * 9 - 1 → ∀ k, (Q.coeff k).natDegree ≤ 25 := by
      intro Q hWQ k
      by_cases hk : Q.coeff k = 0
      · simp [hk]
      · have h1 := wdegBi_le_of_wdeg_coeff hWQ k
        have h2 := wdegBi_ge_natDegree_mul wY (Q.coeff k) hk
        have hle := h2.trans h1
        have hN : 2 * A * 9 - 1 = 26690957 := by norm_num [A]
        have hw : wY = 1048575 := rfl
        rw [hw] at hle; omega
    unfold R_el Polynomial.resultant
    rw [Matrix.det_apply]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
    dsimp only [Function.comp_apply]
    have hsmul : ∀ (u : ℤˣ) (p : BiPoly Fld), (u • p).natDegree ≤ p.natDegree := fun u p => by
      rw [Units.smul_def]; rcases Int.units_eq_one_or u with rfl | rfl <;> simp
    refine (hsmul _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
    calc ∑ i : Fin (dF + dD), (Polynomial.sylvester F0 (contactDeriv F0) dF dD (σ i) i).natDegree
        ≤ ∑ _i : Fin (dF + dD), 25 := by
          apply Finset.sum_le_sum; intro i _
          simp only [Polynomial.sylvester, Matrix.of_apply]
          refine Fin.addCases (fun r => ?_) (fun r => ?_) i
          · simp only [Fin.addCases_left]; split_ifs
            · exact hdeg_coeff _ hW_D _
            · simp
          · simp only [Fin.addCases_right]; split_ifs
            · exact hdeg_coeff F0 hW _
            · simp
      _ = (dF + dD) * 25 := by simp
      _ ≤ 150 := by omega
  exact (card_roots_biPoly_le hRel_ne TF hRel_eval).trans hRel_deg

private lemma mapC_kerDLocalPoly (x0 y0 : Fld) (e : ℕ × ℕ × ℕ × ℕ) :
    (kerDLocalPoly x0 y0 e).map (Polynomial.mapRingHom (Polynomial.mapRingHom Polynomial.C)) =
      kerDLocalPoly (Polynomial.C x0) (Polynomial.C y0) e := by
  let ψ : LocalPoly Fld →+* LocalPoly (Polynomial Fld) :=
    Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.C : Fld →+* Polynomial Fld)))
  change ψ (kerDLocalPoly x0 y0 e) = kerDLocalPoly (Polynomial.C x0) (Polynomial.C y0) e
  have hC : ∀ a : Fld, ψ (locC a) = locC (Polynomial.C a) := fun a => by
    unfold ψ locC; simp [Polynomial.map_C]
  have hR : ψ locR = locR := by unfold ψ locR; simp [Polynomial.map_C, Polynomial.map_X]
  have hW : ψ locW = locW := by unfold ψ locW; simp [Polynomial.map_C, Polynomial.map_X]
  have hT : ψ locT = locT := by unfold ψ locT; simp [Polynomial.map_X]
  have hU : ψ localU = localU := by unfold localU; rw [map_add, map_pow, map_mul, map_pow, hW, hT, hR]
  unfold kerDLocalPoly
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    map_add, map_add, map_mul, map_add, map_add,
    hR, hW, hT, hU, hC, hC, hC, hC, map_pow, map_pow]

/-- **Main Scalar List-Size Bound (`ScalarListBound 10000000`):**
At agreement threshold `A = 1482831`, every received word `u : Idx → Fld` has at most `10^7`
degree-`≤ wY` polynomials agreeing with `u` on `≥ A` coordinates! -/
theorem scalarListBound_6401 : ScalarListBound 10000000 := by
  classical
  intro u T hT
  let W0 : ℕ := 2 * A * 9 - 1
  have hsurp0 : Fintype.card Idx * rankKerD 9 2 * (0 + 1) + 0 * yWeightSum wY W0 2 <
      varsKerDExact wY W0 2 * (0 + 1) := by
    rw [BinaryIRSProfile.card_index]
    norm_num [N, A, wY, W0, rankKerD, varsKerDExact, Finset.sum_range_succ, Finset.sum_range_zero]
  obtain ⟨Qz, q_coord, hQz_eq, hQz_ne, _, hQz_deg, hQz_wdeg, hQz_wYZ, _, hQz_van⟩ :=
    exists_global_contact_interpolant_wtd BinaryIRSProfile.domain (fun i => Polynomial.C (u i))
      (dy := 0) (wY := wY) (W0 := W0) (s0 := 2) (m0 := 9) (D_ZF := 0)
      (by norm_num [wY]) (fun _ => by simp) (by simp) hsurp0
  let Q0 : ContactPoly Fld := evalZContact Qz 0
  have hQ0_sum : Q0 = ∑ e : KerDIdx wY W0 2, cC ((q_coord e).eval 0) * kerDBasisPoly e.1 := by
    dsimp only [Q0]; rw [hQz_eq]; exact evalZContact_sum_kerD q_coord 0
  have hQ0_ne : Q0 ≠ 0 := by
    intro h0; apply hQz_ne
    apply Polynomial.ext; intro k; apply Polynomial.ext; intro j; apply Polynomial.ext; intro i
    have hdeg0 : (((Qz.coeff k).coeff j).coeff i).natDegree = 0 :=
      Nat.eq_zero_of_le_zero (natDegree_Z_le_of_wYZ hQz_wYZ k j i)
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
    have hev0 : (((Qz.coeff k).coeff j).coeff i).eval 0 = 0 := by
      have h1 := congrArg (fun Q : ContactPoly Fld => ((Q.coeff k).coeff j).coeff i) h0
      simpa [Q0, evalZContact] using h1
    rw [hC, Polynomial.eval_C] at hev0
    rw [hC, hev0, map_zero, Polynomial.coeff_zero, Polynomial.coeff_zero, Polynomial.coeff_zero]
  have hQ0_deg : Q0.natDegree ≤ 2 := (Polynomial.natDegree_map_le).trans hQz_deg
  have hQ0_wdeg : wdeg wY Q0 ≤ W0 := by
    rw [wdeg_le_iff]; intro k j i hnz
    have hnz' : ((Qz.coeff k).coeff j).coeff i ≠ 0 := fun h => hnz (by simp [Q0, evalZContact, h])
    exact (wdeg_le_iff wY W0 Qz).mp hQz_wdeg k j i hnz'
  have hQ0_van : ∀ P ∈ T, evalContact Q0 P = 0 := by
    intro P hP
    have ⟨hPdeg, hPcard⟩ := hT P hP
    dsimp only [Q0]; rw [hQz_eq]
    refine evalContact_eq_zero_of_global_coords BinaryIRSProfile.domain (fun i => Polynomial.C (u i))
      (by norm_num [wY]) (by norm_num [W0, A]) q_coord hQz_van 0 P hPdeg
      (Finset.univ.filter fun i : Idx => P.eval (BinaryIRSProfile.domain i) = u i) hPcard ?_
    intro i hi; simpa [Polynomial.eval_C] using (Finset.mem_filter.mp hi).2
  -- UFD factorization of `Q0` in `ContactPoly Fld`!
  let facs := UniqueFactorizationMonoid.normalizedFactors Q0
  let facs0 := facs.filter fun F => F.natDegree = 0
  let facs1 := facs.filter fun F => 1 ≤ F.natDegree
  have hfacs_split : facs = facs0 + facs1 := by
    ext F
    simp only [facs0, facs1, Multiset.count_add, Multiset.count_filter]
    by_cases h0 : F.natDegree = 0
    · simp [h0]
    · simp [h0, show 1 ≤ F.natDegree by omega]
  obtain ⟨uQ, huQ⟩ := UniqueFactorizationMonoid.prod_normalizedFactors (a := Q0) hQ0_ne
  have hQ0_fac : facs0.prod * facs1.prod * (uQ : ContactPoly Fld) = Q0 := by
    rw [← Multiset.prod_add, ← hfacs_split]; exact huQ
  have hfacs0_deg0 : facs0.prod.natDegree = 0 := by
    have hgen : ∀ m : Multiset (ContactPoly Fld), (∀ F ∈ m, F.natDegree = 0) → m.prod.natDegree = 0 := by
      intro m; induction m using Multiset.induction_on with
      | empty => intro _; simp
      | cons a s ih =>
          intro h
          rw [Multiset.prod_cons]
          exact Nat.eq_zero_of_le_zero (Polynomial.natDegree_mul_le.trans
            (by rw [h a (Multiset.mem_cons_self a s), ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))]))
    exact hgen facs0 fun F hF => (Multiset.mem_filter.mp hF).2
  let G0 : BiPoly Fld := facs0.prod.coeff 0
  have hfacs0_eq : facs0.prod = Polynomial.C G0 := Polynomial.eq_C_of_natDegree_eq_zero hfacs0_deg0
  have hG0_ne : G0 ≠ 0 := by
    intro h0; apply hQ0_ne
    rw [← hQ0_fac, hfacs0_eq, h0, map_zero, zero_mul, zero_mul]
  have hG0_deg : G0.natDegree ≤ 25 := by
    have hdvd0 : Polynomial.C G0 ∣ Q0 := ⟨facs1.prod * (uQ : ContactPoly Fld), by rw [← hQ0_fac, hfacs0_eq]; ring⟩
    rcases hdvd0 with ⟨R0, hR0⟩
    have hR0_ne : R0 ≠ 0 := fun h0 => hQ0_ne (by rw [hR0, h0, mul_zero])
    have hwG : wdeg wY (Polynomial.C G0) ≤ W0 := by
      have h1 := wdeg_mul wY (Polynomial.C_ne_zero.mpr hG0_ne) hR0_ne
      rw [← hR0] at h1; omega
    have hwBi : wdegBi wY G0 ≤ W0 := by simpa using wdegBi_le_of_wdeg_coeff hwG 0
    have hmul := wdegBi_ge_natDegree_mul wY G0 hG0_ne
    have hle := hmul.trans hwBi
    have hW0 : W0 = 26690957 := by norm_num [W0, A]
    have hw : wY = 1048575 := rfl
    rw [hw] at hle; omega
  have hfacs1_card : facs1.card ≤ 2 := by
    have hsum : ∀ m : Multiset (ContactPoly Fld), (∀ F ∈ m, Irreducible F ∧ 1 ≤ F.natDegree) →
        m.card ≤ m.prod.natDegree := by
      intro m; induction m using Multiset.induction_on with
      | empty => intro _; simp
      | cons a s ih =>
          intro h
          have ha := h a (Multiset.mem_cons_self a s)
          have hs : ∀ x ∈ s, Irreducible x ∧ 1 ≤ x.natDegree := fun x hx => h x (Multiset.mem_cons_of_mem hx)
          have hs_ne : s.prod ≠ 0 := Multiset.prod_ne_zero (s := s) fun h0 => (hs 0 h0).1.ne_zero rfl
          rw [Multiset.card_cons, Multiset.prod_cons, Polynomial.natDegree_mul ha.1.ne_zero hs_ne]
          have := ih hs; omega
    have h1 := hsum facs1 fun F hF => ⟨UniqueFactorizationMonoid.irreducible_of_normalized_factor F
      (Multiset.mem_filter.mp hF).1, (Multiset.mem_filter.mp hF).2⟩
    have hf1_ne : facs1.prod ≠ 0 := fun h0 => hQ0_ne (by rw [← hQ0_fac, h0, mul_zero, zero_mul])
    have hf0_ne : facs0.prod ≠ 0 := fun h0 => hQ0_ne (by rw [← hQ0_fac, h0, zero_mul, zero_mul])
    have hprod_deg : facs1.prod.natDegree ≤ Q0.natDegree := by
      rw [← hQ0_fac, Polynomial.natDegree_mul (mul_ne_zero hf0_ne hf1_ne) uQ.ne_zero,
        Polynomial.natDegree_mul hf0_ne hf1_ne]
      omega
    omega
  -- Every `P ∈ T` vanishes on either `G0` or some `F0 ∈ facs1.toFinset`!
  have hT_cover : T ⊆ (T.filter fun P => G0.eval P = 0) ∪
      facs1.toFinset.biUnion (fun F0 => T.filter fun P => evalContact F0 P = 0) := by
    intro P hP
    have h0 := hQ0_van P hP
    rw [← hQ0_fac, evalContact_mul, evalContact_mul, hfacs0_eq] at h0
    have hu_ne : evalContact (uQ : ContactPoly Fld) P ≠ 0 := by
      rcases uQ.isUnit with ⟨v, hv⟩
      intro h0'
      have h1 : evalContact (1 : ContactPoly Fld) P = 0 := by
        have hv1 := congrArg (fun q => evalContact q P) v.mul_inv
        rw [evalContact_mul, hv, h0', zero_mul] at hv1; exact hv1.symm
      have : evalContact (1 : ContactPoly Fld) P = 1 := by unfold evalContact; simp
      rw [this] at h1; exact one_ne_zero h1
    have h01 := (mul_eq_zero.mp h0).resolve_right hu_ne
    rcases mul_eq_zero.mp h01 with hG | hFprod
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hP, by simpa [evalContact] using hG⟩)
    · have hex : ∃ F0 ∈ facs1, evalContact F0 P = 0 := by
        have hgen : ∀ m : Multiset (ContactPoly Fld), evalContact m.prod P = 0 → ∃ F0 ∈ m, evalContact F0 P = 0 := by
          intro m; induction m using Multiset.induction_on with
          | empty => intro h; unfold evalContact at h; simp at h
          | cons a s ih =>
              intro h; rw [Multiset.prod_cons, evalContact_mul] at h
              rcases mul_eq_zero.mp h with ha | hs
              · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
              · obtain ⟨F0, hF0, hev⟩ := ih hs; exact ⟨F0, Multiset.mem_cons_of_mem hF0, hev⟩
        exact hgen facs1 hFprod
      obtain ⟨F0, hF0, hev⟩ := hex
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨F0, Multiset.mem_toFinset.mpr hF0,
        Finset.mem_filter.mpr ⟨hP, hev⟩⟩)
  -- Bound each factor `F0 ∈ facs1.toFinset` by `≤ 100000`!
  have hfac_bound : ∀ F0 ∈ facs1.toFinset, (T.filter fun P => evalContact F0 P = 0).card ≤ 100000 := by
    intro F0 hF0
    have hF0_mem : F0 ∈ facs1 := Multiset.mem_toFinset.mp hF0
    have hirr : Irreducible F0 := UniqueFactorizationMonoid.irreducible_of_normalized_factor F0 (Multiset.mem_filter.mp hF0_mem).1
    have hd1 : 1 ≤ F0.natDegree := (Multiset.mem_filter.mp hF0_mem).2
    have hdvd : F0 ∣ Q0 := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_filter.mp hF0_mem).1
    rcases hdvd with ⟨Q', hQ'⟩
    have hQ'_ne : Q' ≠ 0 := fun h0 => hQ0_ne (by rw [hQ', h0, mul_zero])
    have hd2 : F0.natDegree ≤ 2 := by
      have := Polynomial.natDegree_mul hirr.ne_zero hQ'_ne; rw [← hQ'] at this; omega
    have hWF_le : wdeg wY F0 ≤ W0 := by
      have := wdeg_mul wY hirr.ne_zero hQ'_ne; rw [← hQ'] at this; omega
    set TF := T.filter fun P => evalContact F0 P = 0
    by_cases hDF : contactDeriv F0 ≠ 0
    · exact (card_roots_contactDeriv_le hirr hd1 hd2 hWF_le hDF TF (fun P hP => (Finset.mem_filter.mp hP).2)).trans (by omega)
    · push Not at hDF
      set W_F := wdeg wY F0
      have hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ 51 / 2 := by
        have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
        rw [div_le_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 2)]
        have h1 : W_F ≤ 26690957 := by simpa [W0, A] using hWF_le
        have h2 : (W_F : ℚ) ≤ 26690957 := by exact_mod_cast h1
        norm_num [wY]; linarith
      have hirr_rat : Irreducible (liftCRat (cLiftZ F0)) := irreducible_liftCRat_cLiftZ hirr
      have hdeg_lift : (cLiftZ F0).natDegree = F0.natDegree := cLiftZ_natDegree F0
      have hwdeg_lift : wdeg wY (cLiftZ F0) = W_F := cLiftZ_wdeg
      -- Helper to lift local shift exactness from `Fld` to `Fld[Z]` constants!
      have hlocal_lift : ∀ {d : ℕ} (f_coord : KerDIdx wY W_F d → Fld) (i : Idx),
          (∑ e : KerDIdx wY W_F d, locC (Polynomial.C (f_coord e)) * kerDLocalPoly (Polynomial.C (BinaryIRSProfile.domain i)) (Polynomial.C (u i)) e.1) =
          (∑ e : KerDIdx wY W_F d, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1).map
            (Polynomial.mapRingHom (Polynomial.mapRingHom Polynomial.C)) := by
        intro d f_coord i
        let ψ : LocalPoly Fld →+* LocalPoly (Polynomial Fld) :=
          Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.C : Fld →+* Polynomial Fld)))
        change _ = ψ _
        rw [map_sum]
        apply Finset.sum_congr rfl; intro e _
        rw [map_mul]
        exact congrArg₂ (· * ·) (by unfold ψ locC; simp [Polynomial.map_C])
          (mapC_kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1).symm
      have htw_lift : ∀ {d : ℕ} (f_coord : KerDIdx wY W_F d → Fld) (i : Idx) (k_i : ℕ),
          (twOrdGE (∑ e : KerDIdx wY W_F d, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1) k_i →
            twOrdGE (∑ e : KerDIdx wY W_F d, locC (Polynomial.C (f_coord e)) * kerDLocalPoly (Polynomial.C (BinaryIRSProfile.domain i)) (Polynomial.C (u i)) e.1) k_i) ∧
          ((∃ p q, p + q = k_i ∧ twCoeff (∑ e : KerDIdx wY W_F d, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1) p q ≠ 0) →
            ∃ p q, p + q = k_i ∧ twCoeff (∑ e : KerDIdx wY W_F d, locC (Polynomial.C (f_coord e)) * kerDLocalPoly (Polynomial.C (BinaryIRSProfile.domain i)) (Polynomial.C (u i)) e.1) p q ≠ 0) := by
        intro d f_coord i k_i
        rw [hlocal_lift]
        constructor
        · intro h p q hpq
          simp only [twCoeff, Polynomial.coeff_map, Polynomial.coe_mapRingHom]
          change Polynomial.map Polynomial.C (twCoeff _ p q) = 0
          rw [h p q hpq, Polynomial.map_zero]
        · rintro ⟨p, q, hpq, hne⟩
          refine ⟨p, q, hpq, ?_⟩
          simp only [twCoeff, Polynomial.coeff_map, Polynomial.coe_mapRingHom]
          exact (Polynomial.map_ne_zero_iff Polynomial.C_injective).mpr hne
      have hcard_cap : ∀ {d m s : ℕ}, 1 ≤ d → d ≤ 2 → m ≤ 3000 → s ≤ 300 →
          (d * (2 * A * m - 1) + s * (W_F - d * (wY - 1))) / wY ≤ 100000 := by
        intro d m s hd1' hd2' hm3 hs3
        have hW1 : W_F ≤ 26690957 := by simpa [W0, A] using hWF_le
        have hnum : d * (2 * A * m - 1) + s * (W_F - d * (wY - 1)) ≤ 2 * (2 * A * 3000) + 300 * 26690957 := by
          have h1 : d * (2 * A * m - 1) ≤ 2 * (2 * A * 3000) :=
            Nat.mul_le_mul hd2' ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left (2 * A) hm3))
          have h2 : s * (W_F - d * (wY - 1)) ≤ 300 * 26690957 :=
            Nat.mul_le_mul hs3 (by omega)
          omega
        have hdiv : (2 * (2 * A * 3000) + 300 * 26690957) / wY ≤ 100000 := by norm_num [A, wY]
        exact (Nat.div_le_div_right hnum).trans hdiv
      rcases (show F0.natDegree = 1 ∨ F0.natDegree = 2 by omega) with hdF1 | hdF2
      · -- Subcase `dF = 1`:
        obtain ⟨f_coord, hF0_eq, _⟩ := (mem_kerD_iff_exists_unique_coords (wY := wY) (W := W_F) (s := 1) (by norm_num [wY]) F0).mp ⟨hDF, le_of_eq hdF1, le_rfl⟩
        have hf1_ne : F0.coeff 1 ≠ 0 := by
          rw [← hdF1, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
        have hWF_lo : 1 * (wY - 1) ≤ W_F := by
          have := wdegBi_coeff_le_of_wdeg (le_rfl : wdeg wY F0 ≤ W_F) 1 hf1_ne; omega
        let Loc (i : Idx) : LocalPoly Fld := ∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1
        have hLoc_ne : ∀ i : Idx, Loc i ≠ 0 := fun i =>
          localShift_ne_zero (BinaryIRSProfile.domain i) (u i) f_coord (hF0_eq ▸ hirr.ne_zero)
        let k : Idx → ℕ := fun i => exactTwOrd (Loc i)
        have hvan : ∀ i, twOrdGE (Loc i) (k i) := fun i => twOrdGE_exactTwOrd (hLoc_ne i)
        have hfinish1 : ∀ (m s : ℕ), 0 < m → m ≤ 3000 → 1 ≤ s → s ≤ 300 →
            (0 : ℚ) < vquotLbQ 1 m s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ 1 m s (k i)) / (N : ℚ) →
            TF.card ≤ 100000 := fun m s hm hm3 hs hs3 hsurp => by
          have hlift_eq : ∑ e : KerDIdx wY W_F 1, cC (Polynomial.C (f_coord e)) * kerDBasisPoly e.1 = cLiftZ F0 := by
            rw [← cLiftZ_sum_kerDBasisPoly, ← hF0_eq]
          have hcard := card_le_of_degZ_zero_surplus u le_rfl hs hm hWF_lo f_coord
            (by rw [hlift_eq]; exact hirr_rat) (by rw [hlift_eq, hdeg_lift, hdF1])
            (by rw [hlift_eq, hwdeg_lift]) k
            (fun i => ⟨(htw_lift f_coord i (k i)).1 (hvan i), fun _ => (htw_lift f_coord i (k i)).2 (exists_twCoeff_exactTwOrd (hLoc_ne i))⟩)
            hsurp TF (fun P hP => by
              have hPT := (Finset.mem_filter.mp hP).1
              exact ⟨(hT P hPT).1, (hT P hPT).2, by rw [← hF0_eq]; exact (Finset.mem_filter.mp hP).2⟩)
          exact hcard.trans (hcard_cap le_rfl (by omega) hm3 hs3)
        by_cases hemp : TF.Nonempty
        · obtain ⟨P0, hP0⟩ := hemp
          have hP0T := (Finset.mem_filter.mp hP0).1
          have hP0van := (Finset.mem_filter.mp hP0).2
          have hRes_ne_fn : 2 ≤ (F0.coeff 1).natDegree →
              Polynomial.resultant (F0.coeff 0) (F0.coeff 1) (F0.coeff 0).natDegree (F0.coeff 1).natDegree ≠ 0 := by
            intro h2
            have hd1_lift : 1 ≤ ((cLiftZ F0).coeff 1).natDegree := by
              have : ((cLiftZ F0).coeff 1).natDegree = (F0.coeff 1).natDegree := by
                unfold cLiftZ; simp only [Polynomial.coeff_map]
                exact Polynomial.natDegree_map_eq_of_injective (Polynomial.map_injective _ Polynomial.C_injective) _
              omega
            have ⟨_, _, hresZ⟩ := resY_f0_f1_ne_zero_of_irred_deg1 (cLiftZ F0) hirr_rat (by rw [hdeg_lift, hdF1]) hd1_lift
            intro h0; apply hresZ
            have hmap : Polynomial.resultant ((cLiftZ F0).coeff 0) ((cLiftZ F0).coeff 1)
                ((cLiftZ F0).coeff 0).natDegree ((cLiftZ F0).coeff 1).natDegree =
                (Polynomial.resultant (F0.coeff 0) (F0.coeff 1) (F0.coeff 0).natDegree (F0.coeff 1).natDegree).map Polynomial.C := by
              have hd0c : ((cLiftZ F0).coeff 0).natDegree = (F0.coeff 0).natDegree := by
                unfold cLiftZ; simp only [Polynomial.coeff_map]
                exact Polynomial.natDegree_map_eq_of_injective (Polynomial.map_injective _ Polynomial.C_injective) _
              have hd1c : ((cLiftZ F0).coeff 1).natDegree = (F0.coeff 1).natDegree := by
                unfold cLiftZ; simp only [Polynomial.coeff_map]
                exact Polynomial.natDegree_map_eq_of_injective (Polynomial.map_injective _ Polynomial.C_injective) _
              have hc0 : (cLiftZ F0).coeff 0 = (F0.coeff 0).map (Polynomial.mapRingHom Polynomial.C) := by
                unfold cLiftZ; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
              have hc1 : (cLiftZ F0).coeff 1 = (F0.coeff 1).map (Polynomial.mapRingHom Polynomial.C) := by
                unfold cLiftZ; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
              rw [hd0c, hd1c, hc0, hc1]
              exact Polynomial.resultant_map_map (F0.coeff 0) (F0.coeff 1)
                (F0.coeff 0).natDegree (F0.coeff 1).natDegree (Polynomial.mapRingHom Polynomial.C)
            rw [hmap, h0, Polynomial.map_zero]
          by_cases hT4 : (F0.coeff 1).natDegree = 4 ∧ (F0.coeff 0).natDegree ≤ 5 ∧ (W_F : ℚ) / (wY : ℚ) < 28 / 5
          · obtain ⟨hd1_4, hd0_5, hWF_28⟩ := hT4
            have hWF_5lo : 5 * wY ≤ W_F + 1 := by
              have hw1 : wdegBi wY (F0.coeff 1) + (wY - 1) ≤ W_F := by
                simpa only [one_mul] using wdegBi_coeff_le_of_wdeg (le_rfl : wdeg wY F0 ≤ W_F) 1 hf1_ne
              have h1 := wdegBi_ge_natDegree_mul wY (F0.coeff 1) hf1_ne
              rw [hd1_4] at h1
              have hw : 1 ≤ wY := by norm_num [wY]
              omega
            have hWF_6hi : W_F + 1 < 6 * wY := by
              have hwQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
              have hmul : (W_F : ℚ) * 5 < 28 * (wY : ℚ) := by
                have := (div_lt_div_iff₀ hwQ (by norm_num : (0 : ℚ) < 5)).mp hWF_28; linarith
              have hnat : W_F * 5 < 28 * wY := by exact_mod_cast hmul
              have hw : wY = 1048575 := rfl; omega
            have hRes54 : Polynomial.resultant (F0.coeff 0) (F0.coeff 1) 5 4 ≠ 0 := by
              have hres := hRes_ne_fn (by omega); rw [hd1_4] at hres
              exact resultant_54_ne_zero hd0_5 hd1_4 hf1_ne hres
            let mkD0 (P' : Polynomial Fld) (hP' : P' ∈ TF) : KerD45Data :=
              { W_F := W_F, hWF_lo := hWF_5lo, hWF_hi := hWF_6hi, f_coord := f_coord,
                y := u, k := k, hvan := hvan, P := P', hPdeg := (hT P' (Finset.mem_filter.mp hP').1).1,
                Az := Finset.univ.filter fun i : Idx => P'.eval (BinaryIRSProfile.domain i) = u i,
                hAz_card := (hT P' (Finset.mem_filter.mp hP').1).2,
                hagree := fun i hi => (Finset.mem_filter.mp hi).2,
                hFvan := by rw [← hF0_eq]; exact (Finset.mem_filter.mp hP').2,
                hf1_deg := by rw [← hF0_eq]; exact hd1_4,
                hRes_ne := by rw [← hF0_eq]; exact hRes54 }
            have hfrom_wit : ∀ {r : Fin 5}, T4SingleWitness W_F k ∨ T4Std5Witness W_F k r → TF.card ≤ 100000 := by
              intro r hwit
              rcases hwit with ⟨m, s, _, _, δN, δD, _, _, hm, hm3, hs, hs3, _, hδN, hδD, _, hsurp, _⟩ |
                ⟨m, s, _, _, δN, δD, _, _, hm, hm3, hs, hs3, _, hδN, hδD, _, _, hsurp, _⟩
              · have hpos : (0 : ℚ) < (δN : ℚ) / (δD : ℚ) := div_pos (by exact_mod_cast hδN) (by exact_mod_cast hδD)
                exact hfinish1 m s hm hm3 hs hs3 (hpos.trans hsurp)
              · have hpos : (0 : ℚ) < (δN : ℚ) / (δD : ℚ) := div_pos (by exact_mod_cast hδN) (by exact_mod_cast hδD)
                exact hfinish1 m s hm hm3 hs hs3 (hpos.trans hsurp)
            rcases t4_point_dichotomy (mkD0 P0 hP0) hWF_28.le with ⟨p, c, b, hp, hcop, hsyz, hUP0⟩ | hwit
            · by_cases hall : ∀ P' ∈ TF, p.comp (X ^ 2) * P' + b.comp (X ^ 2) + X * c.comp (X ^ 2) = 0
              · have hsub1 : TF ⊆ {P0} := by
                  intro P' hP'; rw [Finset.mem_singleton]
                  have h1 := hall P' hP'
                  have hpsq : p.comp (X ^ 2) ≠ 0 := fun h0 => hp ((comp_X_sq_eq_zero_iff p).mp h0)
                  have hdiff : p.comp (X ^ 2) * (P' - P0) = 0 := by linear_combination h1 - hUP0
                  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hpsq)
                exact (Finset.card_le_card hsub1).trans (by simp)
              · push Not at hall
                obtain ⟨P1, hP1, hUP1⟩ := hall
                have hsyz1 : ∀ j : Fin 3,
                    p * (mkD0 P1 hP1).Pj j + c * (mkD0 P1 hP1).Cj j + b * (mkD0 P1 hP1).Bj j = 0 := fun j => by
                  have hj := hsyz j
                  unfold KerD45Data.Pj KerD45Data.Cj KerD45Data.Bj at hj ⊢
                  dsimp only [mkD0] at hj ⊢
                  exact hj
                exact hfrom_wit (t4_point_syzygy_witness (D := mkD0 P1 hP1) ⟨p, c, b, hp, hcop, hsyz1, hUP1⟩ hWF_28.le)
            · exact hfrom_wit hwit
          · -- Table 1 scalar case!
            obtain ⟨c, _, _, hmpos, hm3, hs3, _, _, hsurp, hcap1, _⟩ :=
              t1_surplus_of_point f_coord u k hvan P0 (hT P0 hP0T).1
                (Finset.univ.filter fun i : Idx => P0.eval (BinaryIRSProfile.domain i) = u i)
                (hT P0 hP0T).2 (fun i hi => (Finset.mem_filter.mp hi).2)
                (by rw [← hF0_eq]; exact hP0van) (by rw [← hF0_eq]; exact hf1_ne) hWF_hi
                (by rw [← hF0_eq]; exact hRes_ne_fn) (by rw [← hF0_eq]; exact hT4)
            have hpars : 1 ≤ c.s ∧ 0 < c.δNum ∧ 0 < c.δDen := by
              unfold checkCapWitness at hcap1
              by_contra hbadp; push Not at hbadp
              have hif : (c.m == 0 || c.s < 1 || c.cHiDen == 0 || c.δNum == 0 || c.δDen == 0 || (1 : ℕ) == 0) = true := by
                rcases lt_or_ge c.s 1 with h1 | h1
                · simp [h1]
                · rcases Nat.eq_zero_or_pos c.δNum with h2 | h2
                  · simp [h2]
                  · have h3 : c.δDen = 0 := by have := hbadp h1 h2; omega
                    simp [h3]
              rw [if_pos hif] at hcap1; cases hcap1
            have hpos : (0 : ℚ) < (c.δNum : ℚ) / (c.δDen : ℚ) := div_pos (by exact_mod_cast hpars.2.1) (by exact_mod_cast hpars.2.2)
            exact hfinish1 c.m c.s hmpos hm3 hpars.1 hs3 (hpos.trans hsurp)
        · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty]; omega
      · -- Subcase `dF = 2`:
        by_cases hf1 : F0.coeff 1 = 0
        · exact False.elim (not_irred_kerD2_coeff1_zero hirr hDF hdF2 hf1)
        · obtain ⟨f_coord, hF0_eq, _⟩ := (mem_kerD_iff_exists_unique_coords (wY := wY) (W := W_F) (s := 2) (by norm_num [wY]) F0).mp ⟨hDF, le_of_eq hdF2, le_rfl⟩
          have hf2_ne : F0.coeff 2 ≠ 0 := by
            rw [← hdF2, Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hirr.ne_zero
          have hWF_lo : 2 * (wY - 1) ≤ W_F :=
            (Nat.le_add_left _ _).trans (wdegBi_coeff_le_of_wdeg (le_rfl : wdeg wY F0 ≤ W_F) 2 hf2_ne)
          have hd1_le25 : (F0.coeff 1).natDegree ≤ 25 := by
            have hw1 := wdegBi_le_of_wdeg_coeff hWF_le 1
            have h1 := wdegBi_ge_natDegree_mul wY (F0.coeff 1) hf1
            have hle := h1.trans hw1
            have hW0 : W0 = 26690957 := by norm_num [W0, A]
            have hw : wY = 1048575 := rfl
            rw [hw, hW0] at hle; omega
          have hd2_le25 : (F0.coeff 2).natDegree ≤ 25 := by
            have hw2 := wdegBi_le_of_wdeg_coeff hWF_le 2
            have h1 := wdegBi_ge_natDegree_mul wY (F0.coeff 2) hf2_ne
            have hle := h1.trans hw2
            have hW0 : W0 = 26690957 := by norm_num [W0, A]
            have hw : wY = 1048575 := rfl
            rw [hw, hW0] at hle; omega
          let TF1 := TF.filter fun P => (F0.coeff 1).eval P = 0
          let TF2 := TF.filter fun P => (F0.coeff 2).eval P = 0
          let TF_cl := TF.filter fun P => (F0.coeff 1).eval P ≠ 0 ∧ (F0.coeff 2).eval P ≠ 0
          have hTF1 : TF1.card ≤ 25 := (card_roots_biPoly_le hf1 TF1 (fun P hP => (Finset.mem_filter.mp hP).2)).trans hd1_le25
          have hTF2 : TF2.card ≤ 25 := (card_roots_biPoly_le hf2_ne TF2 (fun P hP => (Finset.mem_filter.mp hP).2)).trans hd2_le25
          have hTF_split : TF.card ≤ TF_cl.card + 50 := by
            have hsub : TF ⊆ TF_cl ∪ (TF1 ∪ TF2) := by
              intro P hP; simp only [Finset.mem_union, TF_cl, TF1, TF2, Finset.mem_filter]
              by_cases h1 : (F0.coeff 1).eval P = 0
              · exact Or.inr (Or.inl ⟨hP, h1⟩)
              · by_cases h2 : (F0.coeff 2).eval P = 0
                · exact Or.inr (Or.inr ⟨hP, h2⟩)
                · exact Or.inl ⟨hP, h1, h2⟩
            have hle := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
              (Nat.add_le_add_left (Finset.card_union_le _ _) _))
            omega
          have hcl_card : TF_cl.card ≤ 99950 := by
            by_cases hemp : TF_cl.Nonempty
            · obtain ⟨P0, hP0⟩ := hemp
              obtain ⟨hP0F, hP01, hP02⟩ := Finset.mem_filter.mp hP0
              have hP0T := (Finset.mem_filter.mp hP0F).1
              let Loc (i : Idx) : LocalPoly Fld := ∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1
              have hLoc_ne : ∀ i : Idx, Loc i ≠ 0 := fun i =>
                localShift_ne_zero (BinaryIRSProfile.domain i) (u i) f_coord (hF0_eq ▸ hirr.ne_zero)
              let k : Idx → ℕ := fun i => exactTwOrd (Loc i)
              have hvan : ∀ i, twOrdGE (Loc i) (k i) := fun i => twOrdGE_exactTwOrd (hLoc_ne i)
              have hcop_all : ∀ p : Polynomial (RatFunc Fld),
                  p ∣ (F0.coeff 0).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
                  p ∣ (F0.coeff 1).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
                  p ∣ (F0.coeff 2).map (algebraMap (Polynomial Fld) (RatFunc Fld)) →
                  IsUnit p := fun p hp0 hp1 hp2 =>
                no_common_irred_factor_of_irred hirr (by omega) p fun k' => by
                  rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ 3 ≤ k' by omega) with rfl | rfl | rfl | hk3
                  · exact hp0
                  · exact hp1
                  · exact hp2
                  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.map_zero]; exact dvd_zero _
              obtain ⟨m, s, _, _, δN, δD, _, hm, hm3, hs, hs3, _, hδN, hδD, _, hsurp, _⟩ :=
                t23_surplus_of_point f_coord u k hvan P0 (hT P0 hP0T).1
                  (Finset.univ.filter fun i : Idx => P0.eval (BinaryIRSProfile.domain i) = u i)
                  (hT P0 hP0T).2 (fun i hi => (Finset.mem_filter.mp hi).2)
                  (by rw [← hF0_eq]; exact hf1) (by rw [← hF0_eq]; exact hf2_ne)
                  (by rw [← hF0_eq]; exact hP01) (by rw [← hF0_eq]; exact hP02)
                  hWF_hi (by rw [← hF0_eq]; exact hcop_all)
              have hlift_eq : ∑ e : KerDIdx wY W_F 2, cC (Polynomial.C (f_coord e)) * kerDBasisPoly e.1 = cLiftZ F0 := by
                rw [← cLiftZ_sum_kerDBasisPoly, ← hF0_eq]
              have hpos : (0 : ℚ) < (δN : ℚ) / (δD : ℚ) := div_pos (by exact_mod_cast hδN) (by exact_mod_cast hδD)
              have hcard := card_le_of_degZ_zero_surplus u (by omega) hs hm hWF_lo f_coord
                (by rw [hlift_eq]; exact hirr_rat) (by rw [hlift_eq, hdeg_lift, hdF2])
                (by rw [hlift_eq, hwdeg_lift]) k
                (fun i => ⟨(htw_lift f_coord i (k i)).1 (hvan i), fun _ => (htw_lift f_coord i (k i)).2 (exists_twCoeff_exactTwOrd (hLoc_ne i))⟩)
                (hpos.trans hsurp) TF_cl (fun P hP => by
                  have hPF := (Finset.mem_filter.mp hP).1
                  have hPT := (Finset.mem_filter.mp hPF).1
                  exact ⟨(hT P hPT).1, (hT P hPT).2, by rw [← hF0_eq]; exact (Finset.mem_filter.mp hPF).2⟩)
              have hW1 : W_F ≤ 26690957 := by simpa [W0, A] using hWF_le
              have hnum : 2 * (2 * A * m - 1) + s * (W_F - 2 * (wY - 1)) ≤ 2 * (2 * A * 3000) + 300 * 26690957 := by
                have h1 : 2 * (2 * A * m - 1) ≤ 2 * (2 * A * 3000) :=
                  Nat.mul_le_mul_left 2 ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left (2 * A) hm3))
                have h2 : s * (W_F - 2 * (wY - 1)) ≤ 300 * 26690957 :=
                  Nat.mul_le_mul hs3 (by omega)
                omega
              have hdiv : (2 * (2 * A * 3000) + 300 * 26690957) / wY ≤ 99950 := by norm_num [A, wY]
              exact hcard.trans ((Nat.div_le_div_right hnum).trans hdiv)
            · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.card_empty]; omega
          omega
  -- Combine `G0` (`≤ 25`) + at most `2` factors of `deg_R ≥ 1` (`≤ 2 * 100000`)!
  have hG0_card : (T.filter fun P => G0.eval P = 0).card ≤ 25 :=
    (card_roots_biPoly_le hG0_ne _ (fun P hP => (Finset.mem_filter.mp hP).2)).trans hG0_deg
  have hbi_card : (facs1.toFinset.biUnion (fun F0 => T.filter fun P => evalContact F0 P = 0)).card ≤ 200000 := by
    calc _ ≤ ∑ F0 ∈ facs1.toFinset, (T.filter fun P => evalContact F0 P = 0).card := Finset.card_biUnion_le
      _ ≤ ∑ _F0 ∈ facs1.toFinset, 100000 := Finset.sum_le_sum hfac_bound
      _ = facs1.toFinset.card * 100000 := by simp
      _ ≤ facs1.card * 100000 := Nat.mul_le_mul_right _ (Multiset.toFinset_card_le _)
      _ ≤ 2 * 100000 := Nat.mul_le_mul_right _ hfacs1_card
      _ = 200000 := by norm_num
  have htot := (Finset.card_le_card hT_cover).trans (Finset.card_union_le _ _)
  omega

end B6401FactorBound
end ProximityPrize.SubmissionBinaryLower
