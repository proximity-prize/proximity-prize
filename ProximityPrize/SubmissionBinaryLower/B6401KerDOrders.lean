import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 800000

/-!
# Exact local order theorems for `ker(D)` polynomials (Tables 1, 2, 3, 4) & Frobenius `f_1 = 0` descent

Proves the algebraic local vanishing / resultant order bounds for `F ∈ K_{W_F}(d)` (`d ∈ {1, 2}`):
1. `kerD1_local_ords`: If `F ∈ K(1)` has `twOrdGE (localShift x0 y0 F) k`, then
   - `ord_{(t, u)}(A_0) ≥ k`, `ord_{(t, u)}(A_1) ≥ k`, `ord_{(t, u)}(C_0) ≥ k - 1`,
   - hence `mult_{(x0, y0)}(f_0) ≥ 2k - 1` and `mult_{(x0, y0)}(f_1) ≥ 2k - 1`,
   - and `(s, V)`-weighted order (`w = 2`) of `s^2 A_0(s^2, V)^2 + V A_1(s^2, V)^2` is `≥ 4k + 2`!
2. `kerD2_local_ords`: If `F ∈ K(2)` has `twOrdGE (localShift x0 y0 F) k`, then
   - `ord_{(t, u)}(A_0 + u B_2) ≥ k`, `ord_u(A_2(0, u)) ≥ k`, `ord_{(t, u)}(B_2) ≥ k - 2`,
   - `ord_{(t, u)}(A_1) ≥ k`, `ord_{(t, u)}(C_0) ≥ k - 1`, `ord_{(t, u)}(C_1) ≥ k - 1`,
   - hence `mult(f_0) ≥ 2k - 2`, `mult(f_1) ≥ 2k - 1`, `mult(f_2) ≥ 2k - 2`,
   - and `(s, V)`-weighted order (`w = 2`) of `s^4 f_0^2 + V^2 f_2^2 + s^2 V f_1^2` is `≥ 4k + 4`!
3. Exact resultant identities (Tables 1, 3, 4) combining with `pow_dvd_resultant_of_weighted_ord`
   to give `v_ker` and `v_pln` (hence `max(v_ker, v_pln)`)!
4. `frobenius_descent_f1_zero`: Over any finite field `F` of char 2, if `F ∈ K_{W_F}(2)[Z]` has
   `F.coeff 1 = 0`, then `F(X, Y, R, w^2) = H(X, Y, R, w)^2` with `H.natDegree ≤ 1`, `2 * wdeg wY H = wdeg wY F`,
   and `deg_w(H) ≤ deg_Z(F)`!
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401KerDOrders

open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd
open scoped BigOperators

/-! ### Part 1: 2D shifted multiplicity & `(s, V)`-weighted order on `BiPoly A = A[X][Y]` -/

section BivarOrd

variable {A : Type*} [CommRing A]

/-- Shifted bivariate polynomial `f(x0 + s, y0 + v)` in `A[s][v]`. -/
noncomputable def shiftBi (x0 y0 : A) (f : BiPoly A) : BiPoly A :=
  (f.map (Polynomial.compRingHom (C x0 + X))).comp (C (C y0) + X)

/-- Total 2D multiplicity at `(x0, y0)` is at least `m`: every `s^i v^j` with `i + j < m` vanishes. -/
def biMultGE (x0 y0 : A) (f : BiPoly A) (m : ℕ) : Prop :=
  ∀ i j, i + j < m → ((shiftBi x0 y0 f).coeff j).coeff i = 0

/-- Weighted `(s, V)`-order of `P(s, V) ∈ A[s][V]` (with `w(s) = 1, w(V) = w`) is at least `m`:
for every `j`, `s^{m - w * j} ∣ P.coeff j`! -/
def weightedOrdGE (w m : ℕ) (P : BiPoly A) : Prop :=
  ∀ j, X ^ (m - w * j) ∣ P.coeff j

lemma biMultGE_iff_weightedOrdGE_one (x0 y0 : A) (f : BiPoly A) (m : ℕ) :
    biMultGE x0 y0 f m ↔ weightedOrdGE 1 m (shiftBi x0 y0 f) := by
  constructor
  · intro h j
    rw [X_pow_dvd_iff]
    intro i hi
    exact h i j (by omega)
  · intro h i j hij
    have hd := (X_pow_dvd_iff).mp (h j)
    exact hd i (by omega)

lemma shiftBi_add (x0 y0 : A) (f g : BiPoly A) :
    shiftBi x0 y0 (f + g) = shiftBi x0 y0 f + shiftBi x0 y0 g := by
  unfold shiftBi; simp [Polynomial.map_add, add_comp]

lemma shiftBi_mul (x0 y0 : A) (f g : BiPoly A) :
    shiftBi x0 y0 (f * g) = shiftBi x0 y0 f * shiftBi x0 y0 g := by
  unfold shiftBi; simp [Polynomial.map_mul, mul_comp]

lemma shiftBi_C (x0 y0 : A) (p : Polynomial A) :
    shiftBi x0 y0 (C p) = C (p.comp (C x0 + X)) := by
  unfold shiftBi; simp [map_C, C_comp]

lemma shiftBi_X (x0 y0 : A) :
    shiftBi x0 y0 (X : BiPoly A) = C (C y0) + X := by
  unfold shiftBi; simp

lemma shiftBi_pow (x0 y0 : A) (f : BiPoly A) (n : ℕ) :
    shiftBi x0 y0 (f ^ n) = (shiftBi x0 y0 f) ^ n := by
  unfold shiftBi; simp [Polynomial.map_pow, pow_comp]

/-- Exact `resOrdExact` lower bound for `Res_Y(f, g)` from 2D multiplicities at `(x0, y0)`! -/
theorem pow_dvd_resultant_of_biMultGE (x0 y0 : A) (f g : BiPoly A) (df mf dg mg : ℕ)
    (hf : biMultGE x0 y0 f mf) (hg : biMultGE x0 y0 g mg)
    (hdegf : f.natDegree ≤ df) (hdegg : g.natDegree ≤ dg) :
    X ^ resOrdExact df mf dg mg ∣
      Polynomial.resultant (shiftBi x0 y0 f) (shiftBi x0 y0 g) df dg := by
  have h1 : weightedOrdGE 1 mf (shiftBi x0 y0 f) := (biMultGE_iff_weightedOrdGE_one x0 y0 f mf).mp hf
  have h2 : weightedOrdGE 1 mg (shiftBi x0 y0 g) := (biMultGE_iff_weightedOrdGE_one x0 y0 g mg).mp hg
  have hdeg1 : (shiftBi x0 y0 f).natDegree ≤ df := by
    unfold shiftBi
    refine natDegree_comp_le.trans ?_
    have hmap : (f.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ df := natDegree_map_le.trans hdegf
    have hX : (C (C y0) + X : BiPoly A).natDegree ≤ 1 := (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
    nlinarith only [hmap, hX]
  have hdeg2 : (shiftBi x0 y0 g).natDegree ≤ dg := by
    unfold shiftBi
    refine natDegree_comp_le.trans ?_
    have hmap : (g.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ dg := natDegree_map_le.trans hdegg
    have hX : (C (C y0) + X : BiPoly A).natDegree ≤ 1 := (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
    nlinarith only [hmap, hX]
  exact pow_dvd_resultant_exact (X : Polynomial A) (shiftBi x0 y0 f) (shiftBi x0 y0 g)
    df mf dg mg hdeg1 hdeg2 (fun i => by simpa using h1 i) (fun j => by simpa using h2 j)

/-- Exact `X - C x0` divisibility of `Res_Y(f, g)` (invariance of resultant under `Y ↦ Y + y0`
and functoriality under `X ↦ X + x0`)! -/
lemma resultant_shiftBi (x0 y0 : A) (f g : BiPoly A) (df dg : ℕ)
    (hdegf : f.natDegree ≤ df) (hdegg : g.natDegree ≤ dg) :
    Polynomial.resultant (shiftBi x0 y0 f) (shiftBi x0 y0 g) df dg =
      (Polynomial.resultant f g df dg).comp (C x0 + X) := by
  unfold shiftBi
  let φ : Polynomial A →+* Polynomial A := Polynomial.compRingHom (C x0 + X)
  have hmap : Polynomial.resultant (f.map φ) (g.map φ) df dg =
      φ (Polynomial.resultant f g df dg) := Polynomial.resultant_map_map f g df dg φ
  have htrans : ∀ (p q : BiPoly A) (c : Polynomial A),
      p.natDegree ≤ df → q.natDegree ≤ dg →
      Polynomial.resultant (p.comp (C c + X)) (q.comp (C c + X)) df dg =
        Polynomial.resultant p q df dg := by
    intro p q c hp hq
    -- Unipotent upper-triangular matrix M k : Matrix (Fin k) (Fin k) (Polynomial A) of `h ↦ h.comp (C c + X)`!
    let M (k : ℕ) : Matrix (Fin k) (Fin k) (Polynomial A) :=
      Matrix.of fun i j =>
        if i.val ≤ j.val then ((Nat.choose j.val i.val : ℕ) : Polynomial A) * c ^ (j.val - i.val)
        else 0
    have hdetM : ∀ k, (M k).det = 1 := by
      intro k
      have htri : (M k).BlockTriangular id := by
        intro i j hij; dsimp [M]; rw [if_neg (by change j.val < i.val at hij; omega)]
      rw [Matrix.det_of_upperTriangular htri]
      apply Finset.prod_eq_one; intro i _
      dsimp [M]; simp [Nat.choose_self]
    -- Show coeff i (h.comp (C c + X)) = ∑ j : Fin k, M k i j * h.coeff j for any h with natDegree < k (or coeff ≥ k = 0)!
    have hcomp_coeff : ∀ (k : ℕ) (h : BiPoly A), (∀ d ≥ k, h.coeff d = 0) →
        ∀ i : Fin k, (h.comp (C c + X)).coeff i.val = ∑ j : Fin k, M k i j * h.coeff j.val := by
      intro k h hh i
      have hsum : h = ∑ j : Fin k, monomial j.val (h.coeff j.val) := by
        apply Polynomial.ext; intro d; rw [finset_sum_coeff]
        by_cases hd : d < k
        · rw [Finset.sum_eq_single ⟨d, hd⟩]
          · simp [coeff_monomial]
          · intro j _ hne; have : j.val ≠ d := fun he => hne (Fin.ext he); simp [coeff_monomial, this]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        · rw [hh d (by omega)]
          symm; apply Finset.sum_eq_zero; intro j _
          have : j.val ≠ d := by have := j.isLt; omega
          simp [coeff_monomial, this]
      conv_lhs => rw [hsum]
      rw [sum_comp, finset_sum_coeff]
      apply Finset.sum_congr rfl; intro j _
      rw [monomial_comp, coeff_C_mul, mul_comm]
      congr 1
      rw [add_comm, add_pow, finset_sum_coeff]
      dsimp [M]
      by_cases hij : i.val ≤ j.val
      · rw [if_pos hij, Finset.sum_eq_single i.val]
        · rw [show X ^ i.val * C c ^ (j.val - i.val) * (Nat.choose j.val i.val : BiPoly A) =
              C (((Nat.choose j.val i.val : ℕ) : Polynomial A) * c ^ (j.val - i.val)) * X ^ i.val by
            rw [← C_pow, ← C_eq_natCast, map_mul]; ring]
          rw [coeff_C_mul_X_pow, if_pos rfl]
        · intro l _ hne
          rw [show X ^ l * C c ^ (j.val - l) * (Nat.choose j.val l : BiPoly A) =
              C (((Nat.choose j.val l : ℕ) : Polynomial A) * c ^ (j.val - l)) * X ^ l by
            rw [← C_pow, ← C_eq_natCast, map_mul]; ring]
          rw [coeff_C_mul_X_pow, if_neg hne.symm]
        · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
      · rw [if_neg hij]
        apply Finset.sum_eq_zero; intro l hl
        have hne : l ≠ i.val := by have := Finset.mem_range.mp hl; omega
        rw [show X ^ l * C c ^ (j.val - l) * (Nat.choose j.val l : BiPoly A) =
            C (((Nat.choose j.val l : ℕ) : Polynomial A) * c ^ (j.val - l)) * X ^ l by
          rw [← C_pow, ← C_eq_natCast, map_mul]; ring]
        rw [coeff_C_mul_X_pow, if_neg hne.symm]
    -- Block-diagonal matrix B = reindex (M df ⊕ M dg) on Fin (df + dg) has det = 1 and satisfies
    --   M (df + dg) * sylvester p q df dg = sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg * B!
    let B : Matrix (Fin (df + dg)) (Fin (df + dg)) (Polynomial A) :=
      (Matrix.fromBlocks (M df) 0 0 (M dg)).reindex finSumFinEquiv finSumFinEquiv
    have hdetB : B.det = 1 := by
      change ((Matrix.fromBlocks (M df) 0 0 (M dg)).reindex finSumFinEquiv finSumFinEquiv).det = 1
      rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, hdetM, hdetM, mul_one]
    have hSylMul : M (df + dg) * Polynomial.sylvester p q df dg =
        Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg * B := by
      apply Matrix.ext; intro i j
      -- Notice (sylvester p q df dg) column j = coeffs of X^j₁ * q (for j = castAdd j₁) or X^j₂ * p (for j = natAdd j₂)!
      have hcol_g : ∀ (r' : Fin df) (k : Fin (df + dg)),
          Polynomial.sylvester p q df dg k (Fin.castAdd dg r') = (X ^ r'.val * q).coeff k.val := by
        intro r' k
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc, coeff_X_pow_mul']
        split_ifs with h1 h2
        · rfl
        · exfalso; exact h2 h1.1
        · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
        · rfl
      have hcol_f : ∀ (r : Fin dg) (k : Fin (df + dg)),
          Polynomial.sylvester p q df dg k (Fin.natAdd df r) = (X ^ r.val * p).coeff k.val := by
        intro r k
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc, coeff_X_pow_mul']
        split_ifs with h1 h2
        · rfl
        · exfalso; exact h2 h1.1
        · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
        · rfl
      have hp_comp : (p.comp (C c + X)).natDegree ≤ df := by
        exact natDegree_comp_le.trans (by
          have h1 : (C c + X : BiPoly A).natDegree ≤ 1 :=
            (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
          nlinarith only [hp, h1])
      have hq_comp : (q.comp (C c + X)).natDegree ≤ dg := by
        exact natDegree_comp_le.trans (by
          have h1 : (C c + X : BiPoly A).natDegree ≤ 1 :=
            (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
          nlinarith only [hq, h1])
      have hcol_gc : ∀ (r' : Fin df) (k : Fin (df + dg)),
          Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg k (Fin.castAdd dg r') =
            (X ^ r'.val * q.comp (C c + X)).coeff k.val := by
        intro r' k
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc, coeff_X_pow_mul']
        split_ifs with h1 h2
        · rfl
        · exfalso; exact h2 h1.1
        · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
        · rfl
      have hcol_fc : ∀ (r : Fin dg) (k : Fin (df + dg)),
          Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg k (Fin.natAdd df r) =
            (X ^ r.val * p.comp (C c + X)).coeff k.val := by
        intro r k
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc, coeff_X_pow_mul']
        split_ifs with h1 h2
        · rfl
        · exfalso; exact h2 h1.1
        · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
        · rfl
      induction j using Fin.addCases with
      | left r' =>
          rw [Matrix.mul_apply, Matrix.mul_apply]
          have hLHS : (∑ k : Fin (df + dg), M (df + dg) i k * Polynomial.sylvester p q df dg k (Fin.castAdd dg r')) =
              ((X ^ r'.val * q).comp (C c + X)).coeff i.val := by
            simp_rw [hcol_g]
            symm; apply hcomp_coeff
            intro d hd
            exact coeff_eq_zero_of_natDegree_lt
              ((natDegree_mul_le.trans (Nat.add_le_add (natDegree_X_pow_le r'.val) hq)).trans_lt (by have := r'.isLt; omega))
          have hRHS : (∑ k : Fin (df + dg),
              Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg i k * B k (Fin.castAdd dg r')) =
              ∑ l : Fin df, (X ^ l.val * q.comp (C c + X)).coeff i.val * M df l r' := by
            rw [Fin.sum_univ_add]
            have h0 : (∑ l : Fin dg, Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg i (Fin.natAdd df l) *
                B (Fin.natAdd df l) (Fin.castAdd dg r')) = 0 := by
              apply Finset.sum_eq_zero; intro l _
              simp [B, Matrix.reindex_apply, Matrix.submatrix_apply]
            rw [h0, add_zero]
            apply Finset.sum_congr rfl; intro l _
            rw [hcol_gc]
            simp [B, Matrix.reindex_apply, Matrix.submatrix_apply]
          rw [hLHS, hRHS, mul_comp, pow_comp, X_comp]
          -- Expand (C c + X)^r' = ∑ l : Fin df, C (M df l r') * X^l!
          have hpow_r : (C c + X : BiPoly A) ^ r'.val = ∑ l : Fin df, C (M df l r') * X ^ l.val := by
            apply Polynomial.ext; intro d; rw [finset_sum_coeff]
            have h := hcomp_coeff df (X ^ r'.val) (fun d' hd' => by
              rw [coeff_X_pow]; exact if_neg (by have := r'.isLt; omega))
            by_cases hd : d < df
            · have hd' := h ⟨d, hd⟩
              rw [pow_comp, X_comp] at hd'
              rw [hd', Finset.sum_eq_single r']
              · simp only [coeff_X_pow, if_pos rfl, mul_one]
                rw [Finset.sum_eq_single ⟨d, hd⟩]
                · simp [coeff_C_mul_X_pow]
                · intro l _ hne; have : d ≠ l.val := fun he => hne (Fin.ext he.symm)
                  simp [coeff_C_mul_X_pow, this]
                · intro hnot; exact absurd (Finset.mem_univ _) hnot
              · intro j _ hne; have : j.val ≠ r'.val := fun he => hne (Fin.ext he)
                simp [coeff_X_pow, this]
              · intro hnot; exact absurd (Finset.mem_univ _) hnot
            · have h0 : ((C c + X : BiPoly A) ^ r'.val).coeff d = 0 := by
                apply coeff_eq_zero_of_natDegree_lt
                have h1 : (C c + X : BiPoly A).natDegree ≤ 1 :=
                  (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
                exact (natDegree_pow_le.trans (by nlinarith only [h1])).trans_lt (by have := r'.isLt; omega)
              rw [h0]; symm; apply Finset.sum_eq_zero; intro l _
              rw [coeff_C_mul_X_pow, if_neg (by have := l.isLt; omega)]
          rw [hpow_r, Finset.sum_mul, finset_sum_coeff]
          apply Finset.sum_congr rfl; intro l _
          rw [mul_assoc, coeff_C_mul, mul_comm]
      | right r =>
          rw [Matrix.mul_apply, Matrix.mul_apply]
          have hLHS : (∑ k : Fin (df + dg), M (df + dg) i k * Polynomial.sylvester p q df dg k (Fin.natAdd df r)) =
              ((X ^ r.val * p).comp (C c + X)).coeff i.val := by
            simp_rw [hcol_f]
            symm; apply hcomp_coeff
            intro d hd
            exact coeff_eq_zero_of_natDegree_lt
              ((natDegree_mul_le.trans (Nat.add_le_add (natDegree_X_pow_le r.val) hp)).trans_lt (by have := r.isLt; omega))
          have hRHS : (∑ k : Fin (df + dg),
              Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg i k * B k (Fin.natAdd df r)) =
              ∑ l : Fin dg, (X ^ l.val * p.comp (C c + X)).coeff i.val * M dg l r := by
            rw [Fin.sum_univ_add]
            have h0 : (∑ l : Fin df, Polynomial.sylvester (p.comp (C c + X)) (q.comp (C c + X)) df dg i (Fin.castAdd dg l) *
                B (Fin.castAdd dg l) (Fin.natAdd df r)) = 0 := by
              apply Finset.sum_eq_zero; intro l _
              simp [B, Matrix.reindex_apply, Matrix.submatrix_apply]
            rw [h0, zero_add]
            apply Finset.sum_congr rfl; intro l _
            rw [hcol_fc]
            simp [B, Matrix.reindex_apply, Matrix.submatrix_apply]
          rw [hLHS, hRHS, mul_comp, pow_comp, X_comp]
          have hpow_r : (C c + X : BiPoly A) ^ r.val = ∑ l : Fin dg, C (M dg l r) * X ^ l.val := by
            apply Polynomial.ext; intro d; rw [finset_sum_coeff]
            have h := hcomp_coeff dg (X ^ r.val) (fun d' hd' => by
              rw [coeff_X_pow]; exact if_neg (by have := r.isLt; omega))
            by_cases hd : d < dg
            · have hd' := h ⟨d, hd⟩
              rw [pow_comp, X_comp] at hd'
              rw [hd', Finset.sum_eq_single r]
              · simp only [coeff_X_pow, if_pos rfl, mul_one]
                rw [Finset.sum_eq_single ⟨d, hd⟩]
                · simp [coeff_C_mul_X_pow]
                · intro l _ hne; have : d ≠ l.val := fun he => hne (Fin.ext he.symm)
                  simp [coeff_C_mul_X_pow, this]
                · intro hnot; exact absurd (Finset.mem_univ _) hnot
              · intro j _ hne; have : j.val ≠ r.val := fun he => hne (Fin.ext he)
                simp [coeff_X_pow, this]
              · intro hnot; exact absurd (Finset.mem_univ _) hnot
            · have h0 : ((C c + X : BiPoly A) ^ r.val).coeff d = 0 := by
                apply coeff_eq_zero_of_natDegree_lt
                have h1 : (C c + X : BiPoly A).natDegree ≤ 1 :=
                  (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
                exact (natDegree_pow_le.trans (by nlinarith only [h1])).trans_lt (by have := r.isLt; omega)
              rw [h0]; symm; apply Finset.sum_eq_zero; intro l _
              rw [coeff_C_mul_X_pow, if_neg (by have := l.isLt; omega)]
          rw [hpow_r, Finset.sum_mul, finset_sum_coeff]
          apply Finset.sum_congr rfl; intro l _
          rw [mul_assoc, coeff_C_mul, mul_comm]
    have hdet := congrArg Matrix.det hSylMul
    rw [Matrix.det_mul, Matrix.det_mul, hdetM, hdetB, one_mul, mul_one] at hdet
    exact hdet.symm
  rw [htrans (f.map φ) (g.map φ) (C y0) (natDegree_map_le.trans hdegf) (natDegree_map_le.trans hdegg), hmap]
  rfl

end BivarOrd

/-! ### Part 2: Exact char-2 local order extraction for `deg_R = 1` and `deg_R = 2` in `ker(D)` -/

section KerDLocalOrders

variable {F : Type*} [Field F] [CharP F 2]

/-- Extract the 3 shifted `(t, u)` bivariate parts `(A0, A1, C0)` of a `deg_R ≤ 1` element of `ker(D)`:
`localShift(F) = A0(t, u) + R * A1(t, u) + w * C0(t, u)`!
By `localBasis_linearIndependent_mod`, `twOrdGE (localShift F) k` IMMEDIATELY forces
`ord(A0) ≥ k`, `ord(A1) ≥ k`, and `ord(C0) ≥ k - 1`! -/
theorem kerD1_local_ords {wY W_F k : ℕ} (hwY : 0 < wY) (x0 y0 : F)
    (f_coord : KerDIdx wY W_F 1 → F)
    (hvan : twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) k) :
    let Fpoly : ContactPoly F := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
    biMultGE x0 y0 (Fpoly.coeff 0) (2 * k - 1) ∧
    biMultGE x0 y0 (Fpoly.coeff 1) (2 * k - 1) := by
  -- Express localShift(F) directly in the free basis LocalBasisIdx k 1!
  -- Because s = 1, every (k1, r1, b1, a1) ∈ KerDIdx wY W_F 1 has k1 + r1 ≤ 1, so:
  --   (k1, r1) ∈ {(0, 0), (1, 0), (0, 1)}!
  -- Therefore kerDLocalPoly x0 y0 e ALREADY has q + j ≤ 1, meaning j < 2 AUTOMATICALLY — NO t R^2 reduction ever occurs!
  -- Every monomial t^a' u^b' (q=0, j=0), R t^a' u^b' (q=0, j=1), w t^a' u^b' (q=1, j=0) with q + a' + b' < k
  -- is ALREADY an element of LocalBasisIdx k 1!!
  -- Hence by `localBasis_linearIndependent_mod`, ALL coefficients with a' + b' < k (for A0, A1) and a' + b' < k - 1 (for C0) are ZERO!
  intro Fpoly
  -- Define shifted coefficients A0(a', b'), A1(a', b'), C0(a', b')!
  let A0 (a' b' : ℕ) : F :=
    ∑ e : KerDIdx wY W_F 1,
      if e.1.1 = 0 ∧ e.1.2.1 = 0 then
        f_coord e * (Nat.choose e.1.2.2.2 a' : F) * (x0 ^ 2) ^ (e.1.2.2.2 - a') *
          ((Nat.choose e.1.2.2.1 b' : F) * (y0 ^ 2) ^ (e.1.2.2.1 - b'))
      else if e.1.1 = 0 ∧ e.1.2.1 = 1 then
        f_coord e * y0 * (Nat.choose e.1.2.2.2 a' : F) * (x0 ^ 2) ^ (e.1.2.2.2 - a') *
          ((Nat.choose e.1.2.2.1 b' : F) * (y0 ^ 2) ^ (e.1.2.2.1 - b'))
      else 0
  let A1 (a' b' : ℕ) : F :=
    ∑ e : KerDIdx wY W_F 1,
      if e.1.1 = 1 ∧ e.1.2.1 = 0 then
        f_coord e * (Nat.choose e.1.2.2.2 a' : F) * (x0 ^ 2) ^ (e.1.2.2.2 - a') *
          ((Nat.choose e.1.2.2.1 b' : F) * (y0 ^ 2) ^ (e.1.2.2.1 - b'))
      else if e.1.1 = 0 ∧ e.1.2.1 = 1 then
        f_coord e * x0 * (Nat.choose e.1.2.2.2 a' : F) * (x0 ^ 2) ^ (e.1.2.2.2 - a') *
          ((Nat.choose e.1.2.2.1 b' : F) * (y0 ^ 2) ^ (e.1.2.2.1 - b'))
      else 0
  let C0 (a' b' : ℕ) : F :=
    ∑ e : KerDIdx wY W_F 1,
      if e.1.1 = 0 ∧ e.1.2.1 = 1 then
        f_coord e * (Nat.choose e.1.2.2.2 a' : F) * (x0 ^ 2) ^ (e.1.2.2.2 - a') *
          ((Nat.choose e.1.2.2.1 b' : F) * (y0 ^ 2) ^ (e.1.2.2.1 - b'))
      else 0
  -- Note: for every idx : LocalBasisIdx k 1, kerDLocalNF k 1 x0 y0 e idx equals the exact coefficient of A0, A1, C0!
  have hNF0 : ∀ idx : LocalBasisIdx k 1,
      (∑ e : KerDIdx wY W_F 1, f_coord e * kerDLocalNF k 1 x0 y0 e.1 idx) = 0 := by
    apply localBasis_linearIndependent_mod k 1
    -- localShift F - ∑ idx, NF * basis ∈ (t, w)^k, and localShift F ∈ (t, w)^k, so ∑ idx, NF * basis ∈ (t, w)^k!
    have hdiff : twOrdGE ((∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) -
        ∑ idx : LocalBasisIdx k 1, locC (∑ e : KerDIdx wY W_F 1, f_coord e * kerDLocalNF k 1 x0 y0 e.1 idx) *
          localBasisElem idx.1) k := by
      have hrew : (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) -
          ∑ idx : LocalBasisIdx k 1, locC (∑ e : KerDIdx wY W_F 1, f_coord e * kerDLocalNF k 1 x0 y0 e.1 idx) *
            localBasisElem idx.1 =
          ∑ e : KerDIdx wY W_F 1, locC (f_coord e) *
            (kerDLocalPoly x0 y0 e.1 -
              ∑ idx : LocalBasisIdx k 1, locC (kerDLocalNF k 1 x0 y0 e.1 idx) * localBasisElem idx.1) := by
        simp_rw [locC, map_sum, Finset.sum_mul]
        rw [Finset.sum_comm, ← Finset.sum_sub_distrib (G := LocalPoly F)]
        apply Finset.sum_congr rfl; intro e _
        have hms : ∀ x y z : LocalPoly F, x * (y - z) = x * y - x * z := fun x y z =>
          eq_sub_of_add_eq (G := LocalPoly F) (by rw [← mul_add, sub_add_cancel (G := LocalPoly F)])
        rw [hms]
        refine congrArg₂ (· - ·) rfl ?_
        refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
        simp only [map_mul, mul_assoc]
      rw [hrew]
      have hsum_tw : ∀ (S : Finset (KerDIdx wY W_F 1)) (f : KerDIdx wY W_F 1 → LocalPoly F),
          (∀ e ∈ S, twOrdGE (f e) k) → twOrdGE (∑ e ∈ S, f e) k := by
        intro S f hf; classical
        induction S using Finset.induction_on with
        | empty => simp [twOrdGE_of_zero]
        | insert a S ha ih =>
            rw [Finset.sum_insert ha]
            exact twOrdGE_add (hf a (Finset.mem_insert_self _ _))
              (ih fun y hy => hf y (Finset.mem_insert_of_mem hy))
      apply hsum_tw; intro e _
      have hmem := (mem_kerDIdxFinset_iff wY W_F 1 hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      simpa using twOrdGE_mul (twOrdGE_zero _)
        (twOrdGE_kerDLocalPoly_sub_NF k 1 x0 y0 e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 hmem.1 hmem.2.1)
    have hcomb := twOrdGE_sub hvan hdiff
    rw [sub_sub_cancel (G := LocalPoly F)] at hcomb
    exact hcomb
  -- Evaluate hNF0 at (0, 0, a', b'), (0, 1, a', b'), (1, 0, a', b') to show A0=0, A1=0 (a'+b' < k), C0=0 (a'+b'+1 < k)!
  have hred_self : ∀ (q j a' b' : ℕ) (idx : LocalBasisIdx k 1),
      j < 2 → q + a' + b' < k →
      reduceMonomialCoords k 1 q j a' b' idx = if idx.1 = (q, j, a', b') then 1 else 0 := by
    intro q j a' b' idx hj hlt
    cases a' with
    | zero => rfl
    | succ a'' =>
        unfold reduceMonomialCoords
        have h1 : ¬ (q + (a'' + 1) + b' ≥ k) := by omega
        simp [h1, hj]
  have hred_ge : ∀ (q j a' b' : ℕ) (idx : LocalBasisIdx k 1),
      j < 2 → q + a' + b' ≥ k → reduceMonomialCoords k 1 q j a' b' idx = 0 := by
    intro q j a' b' idx hj hge
    cases a' with
    | zero =>
        unfold reduceMonomialCoords
        have hne : idx.1 ≠ (q, j, 0, b') := by
          intro h
          rcases idx with ⟨⟨q', j', a'', b''⟩, hidx⟩
          have hlt := ((mem_localBasisFinset_iff k 1 q' j' a'' b'').mp hidx).2.1
          simp only [Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl, rfl⟩
          omega
        simp [hne]
    | succ a'' =>
        unfold reduceMonomialCoords
        simp [hge]
  have hred_any : ∀ (q j a' b' : ℕ) (idx : LocalBasisIdx k 1),
      j < 2 → reduceMonomialCoords k 1 q j a' b' idx = if idx.1 = (q, j, a', b') then 1 else 0 := by
    intro q j a' b' idx hj
    by_cases hlt : q + a' + b' < k
    · exact hred_self q j a' b' idx hj hlt
    · rw [hred_ge q j a' b' idx hj (by omega)]
      have hne : idx.1 ≠ (q, j, a', b') := by
        intro h
        rcases idx with ⟨⟨q', j', a'', b''⟩, hidx⟩
        have hlt2 := ((mem_localBasisFinset_iff k 1 q' j' a'' b'').mp hidx).2.1
        simp only [Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl, rfl⟩
        omega
      simp [hne]
  have hA0_zero : ∀ a' b', a' + b' < k → A0 a' b' = 0 := by
    intro a' b' hlt
    let idx : LocalBasisIdx k 1 := ⟨(0, 0, a', b'), (mem_localBasisFinset_iff k 1 0 0 a' b').mpr ⟨by omega, by omega, Or.inl (by omega)⟩⟩
    have h0 := hNF0 idx
    rw [← h0]
    dsimp [A0]; apply Finset.sum_congr rfl; intro e _
    rcases e with ⟨⟨k1, r1, b1, a1⟩, he⟩
    have hmem := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
    unfold kerDLocalNF
    -- Only (k1, r1) ∈ {(0, 0), (1, 0), (0, 1)} are possible!
    have hcases : (k1 = 0 ∧ r1 = 0) ∨ (k1 = 1 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [true_and, ↓reduceIte, hred_any 0 0 _ _ idx (by omega), idx, Prod.mk.injEq,
        true_and]
      by_cases ha : a' ≤ a1
      · by_cases hb : b' ≤ b1
        · rw [Finset.sum_eq_single a', Finset.sum_eq_single b']
          · simp; ring
          · intro b'' _ hne; simp [hne.symm]
          · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
          · intro a'' _ hne
            apply Finset.sum_eq_zero; intro b'' _; simp [hne.symm]
          · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
        · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := b') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
          symm; rw [mul_eq_zero]; right
          apply Finset.sum_eq_zero; intro a'' _; apply Finset.sum_eq_zero; intro b'' hb''
          have hne : b' ≠ b'' := by have := Finset.mem_range.mp hb''; omega
          simp [hne]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right
        apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have hne : a' ≠ a'' := by have := Finset.mem_range.mp ha''; omega
        simp [hne]
    · simp only [one_ne_zero, false_and, ↓reduceIte, hred_any 0 1 _ _ idx (by omega), idx,
        Prod.mk.injEq, zero_ne_one, and_false, false_and, Nat.cast_zero, mul_zero,
        Finset.sum_const_zero]
    · simp only [one_ne_zero, and_false, ↓reduceIte, true_and,
        hred_any 0 0 _ _ idx (by omega), hred_any 0 1 _ _ idx (by omega), hred_any 1 0 _ _ idx (by omega),
        idx, Prod.mk.injEq, zero_ne_one, and_false, false_and, Nat.cast_zero, mul_zero, add_zero]
      by_cases ha : a' ≤ a1
      · by_cases hb : b' ≤ b1
        · rw [Finset.sum_eq_single a', Finset.sum_eq_single b']
          · simp; ring
          · intro b'' _ hne; simp [hne.symm]
          · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
          · intro a'' _ hne
            apply Finset.sum_eq_zero; intro b'' _; simp [hne.symm]
          · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
        · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := b') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
          symm; rw [mul_eq_zero]; right
          apply Finset.sum_eq_zero; intro a'' _; apply Finset.sum_eq_zero; intro b'' hb''
          have hne : b' ≠ b'' := by have := Finset.mem_range.mp hb''; omega
          simp [hne]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right
        apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have hne : a' ≠ a'' := by have := Finset.mem_range.mp ha''; omega
        simp [hne]
  have hA1_zero : ∀ a' b', a' + b' < k → A1 a' b' = 0 := by
    intro a' b' hlt
    let idx : LocalBasisIdx k 1 := ⟨(0, 1, a', b'), (mem_localBasisFinset_iff k 1 0 1 a' b').mpr ⟨by omega, by omega, Or.inl (by omega)⟩⟩
    have h0 := hNF0 idx
    rw [← h0]
    dsimp [A1]; apply Finset.sum_congr rfl; intro e _
    rcases e with ⟨⟨k1, r1, b1, a1⟩, he⟩
    have hmem := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
    unfold kerDLocalNF
    have hcases : (k1 = 0 ∧ r1 = 0) ∨ (k1 = 1 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [zero_ne_one, false_and, ↓reduceIte, hred_any 0 0 _ _ idx (by omega), idx,
        Prod.mk.injEq, one_ne_zero, and_false, false_and, Nat.cast_zero, mul_zero,
        Finset.sum_const_zero]
    · simp only [true_and, ↓reduceIte, hred_any 0 1 _ _ idx (by omega), idx, Prod.mk.injEq,
        true_and]
      by_cases ha : a' ≤ a1
      · by_cases hb : b' ≤ b1
        · rw [Finset.sum_eq_single a', Finset.sum_eq_single b']
          · simp; ring
          · intro b'' _ hne; simp [hne.symm]
          · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
          · intro a'' _ hne; apply Finset.sum_eq_zero; intro b'' _; simp [hne.symm]
          · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
        · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := b') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
          symm; rw [mul_eq_zero]; right
          apply Finset.sum_eq_zero; intro a'' _; apply Finset.sum_eq_zero; intro b'' hb''
          have hne : b' ≠ b'' := by have := Finset.mem_range.mp hb''; omega
          simp [hne]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right
        apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have hne : a' ≠ a'' := by have := Finset.mem_range.mp ha''; omega
        simp [hne]
    · simp only [zero_ne_one, false_and, ↓reduceIte, true_and, one_ne_zero,
        hred_any 0 0 _ _ idx (by omega), hred_any 0 1 _ _ idx (by omega), hred_any 1 0 _ _ idx (by omega),
        idx, Prod.mk.injEq, one_ne_zero, zero_ne_one, and_false, false_and, Nat.cast_zero, mul_zero,
        zero_add, add_zero]
      by_cases ha : a' ≤ a1
      · by_cases hb : b' ≤ b1
        · rw [Finset.sum_eq_single a', Finset.sum_eq_single b']
          · simp; ring
          · intro b'' _ hne; simp [hne.symm]
          · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
          · intro a'' _ hne; apply Finset.sum_eq_zero; intro b'' _; simp [hne.symm]
          · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
        · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := b') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
          symm; rw [mul_eq_zero]; right
          apply Finset.sum_eq_zero; intro a'' _; apply Finset.sum_eq_zero; intro b'' hb''
          have hne : b' ≠ b'' := by have := Finset.mem_range.mp hb''; omega
          simp [hne]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right
        apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have hne : a' ≠ a'' := by have := Finset.mem_range.mp ha''; omega
        simp [hne]
  have hC0_zero : ∀ a' b', 1 + a' + b' < k → C0 a' b' = 0 := by
    intro a' b' hlt
    let idx : LocalBasisIdx k 1 := ⟨(1, 0, a', b'), (mem_localBasisFinset_iff k 1 1 0 a' b').mpr ⟨by omega, by omega, Or.inl (by omega)⟩⟩
    have h0 := hNF0 idx
    rw [← h0]
    dsimp [C0]; apply Finset.sum_congr rfl; intro e _
    rcases e with ⟨⟨k1, r1, b1, a1⟩, he⟩
    have hmem := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
    unfold kerDLocalNF
    have hcases : (k1 = 0 ∧ r1 = 0) ∨ (k1 = 1 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [zero_ne_one, and_false, ↓reduceIte, hred_any 0 0 _ _ idx (by omega), idx,
        Prod.mk.injEq, one_ne_zero, false_and, Nat.cast_zero, mul_zero, Finset.sum_const_zero]
    · simp only [one_ne_zero, false_and, ↓reduceIte, hred_any 0 1 _ _ idx (by omega), idx,
        Prod.mk.injEq, one_ne_zero, false_and, Nat.cast_zero, mul_zero, Finset.sum_const_zero]
    · simp only [true_and, one_ne_zero, ↓reduceIte,
        hred_any 0 0 _ _ idx (by omega), hred_any 0 1 _ _ idx (by omega), hred_any 1 0 _ _ idx (by omega),
        idx, Prod.mk.injEq, one_ne_zero, false_and, Nat.cast_zero, mul_zero, zero_add]
      by_cases ha : a' ≤ a1
      · by_cases hb : b' ≤ b1
        · rw [Finset.sum_eq_single a', Finset.sum_eq_single b']
          · simp; ring
          · intro b'' _ hne; simp [hne.symm]
          · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
          · intro a'' _ hne; apply Finset.sum_eq_zero; intro b'' _; simp [hne.symm]
          · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
        · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := b') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
          symm; rw [mul_eq_zero]; right
          apply Finset.sum_eq_zero; intro a'' _; apply Finset.sum_eq_zero; intro b'' hb''
          have hne : b' ≠ b'' := by have := Finset.mem_range.mp hb''; omega
          simp [hne]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right
        apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have hne : a' ≠ a'' := by have := Finset.mem_range.mp ha''; omega
        simp [hne]
  -- Now read off shiftBi x0 y0 (Fpoly.coeff 0) and shiftBi x0 y0 (Fpoly.coeff 1) in terms of A0, A1, C0!
  -- Specifically:
  --   coeff (2*b') (2*a') of shiftBi(f0) = A0 a' b'
  --   coeff (2*b'+1) (2*a') of shiftBi(f0) = C0 a' b'
  --   all odd-s coefficients of shiftBi(f0) = 0!
  --   coeff (2*b') (2*a') of shiftBi(f1) = A1 a' b'
  --   coeff (2*b') (2*a'+1) of shiftBi(f1) = C0 a' b'
  --   all odd-v coefficients of shiftBi(f1) = 0!
  have hpow_even : ∀ (c : F) (n : ℕ), ((C c + X : Polynomial F) ^ 2) ^ n =
      ∑ l ∈ Finset.range (n + 1), C ((Nat.choose n l : F) * (c ^ 2) ^ (n - l)) * X ^ (2 * l) := by
    intro c n
    have hsq : (C c + X : Polynomial F) ^ 2 = C (c ^ 2) + X ^ 2 := by
      have h2 : (2 : Polynomial F) = 0 := by
        rw [show (2 : Polynomial F) = C (2 : F) by
          rw [show (2 : Polynomial F) = 1 + 1 by ring, show (2 : F) = 1 + 1 by ring, map_add, map_one],
          CharTwo.two_eq_zero, map_zero]
      calc (C c + X : Polynomial F) ^ 2 = C c ^ 2 + 2 * C c * X + X ^ 2 := by ring
        _ = C (c ^ 2) + X ^ 2 := by rw [h2, ← map_pow]; ring
    rw [hsq, add_comm, add_pow]
    apply Finset.sum_congr rfl; intro l _
    rw [← pow_mul, ← map_pow, mul_assoc, show C ((c ^ 2) ^ (n - l)) * (Nat.choose n l : Polynomial F) =
      C ((Nat.choose n l : F) * (c ^ 2) ^ (n - l)) by simp [mul_comm], mul_comm]
  have hpow_even_Y : ∀ (c : F) (n : ℕ), ((C (C c) + X : BiPoly F) ^ 2) ^ n =
      ∑ l ∈ Finset.range (n + 1), C (C ((Nat.choose n l : F) * (c ^ 2) ^ (n - l))) * X ^ (2 * l) := by
    intro c n
    have hsq : (C (C c) + X : BiPoly F) ^ 2 = C (C (c ^ 2)) + X ^ 2 := by
      have h2 : (2 : BiPoly F) = 0 := by
        rw [show (2 : BiPoly F) = C (C (2 : F)) by
          rw [show (2 : BiPoly F) = 1 + 1 by ring, show (2 : F) = 1 + 1 by ring, map_add, map_one, map_add, map_one],
          CharTwo.two_eq_zero, map_zero, map_zero]
      calc (C (C c) + X : BiPoly F) ^ 2 = C (C c) ^ 2 + 2 * C (C c) * X + X ^ 2 := by ring
        _ = C (C (c ^ 2)) + X ^ 2 := by rw [h2, ← map_pow, ← map_pow]; ring
    rw [hsq, add_comm, add_pow]
    apply Finset.sum_congr rfl; intro l _
    rw [← pow_mul, ← map_pow, ← map_pow, mul_assoc,
      show C (C ((c ^ 2) ^ (n - l))) * (Nat.choose n l : BiPoly F) =
        C (C ((Nat.choose n l : F) * (c ^ 2) ^ (n - l))) by simp [mul_comm], mul_comm]
  have hshift_f0 : ∀ i j, ((shiftBi x0 y0 (Fpoly.coeff 0)).coeff j).coeff i =
      if i % 2 = 0 ∧ j % 2 = 0 then A0 (i / 2) (j / 2)
      else if i % 2 = 0 ∧ j % 2 = 1 then C0 (i / 2) (j / 2)
      else 0 := by
    intro i j
    -- Expand Fpoly.coeff 0 = ∑ e, C (C (f_coord e)) * (kerDBasisPoly e.1).coeff 0
    have hf0 : Fpoly.coeff 0 =
        ∑ e : KerDIdx wY W_F 1,
          if e.1.1 = 0 ∧ e.1.2.1 = 0 then
            C (C (f_coord e)) * (C (X ^ 2) ^ e.1.2.2.2) * (X ^ 2) ^ e.1.2.2.1
          else if e.1.1 = 0 ∧ e.1.2.1 = 1 then
            C (C (f_coord e)) * X * (C (X ^ 2) ^ e.1.2.2.2) * (X ^ 2) ^ e.1.2.2.1
          else 0 := by
      dsimp [Fpoly]; rw [finset_sum_coeff]
      apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
      have hmem := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
      have hcases : (k1 = 0 ∧ r1 = 0) ∨ (k1 = 1 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [true_and, ↓reduceIte]
        unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_zero, one_mul, one_mul,
          show C (C (C (f_coord ⟨(0, 0, b1, a1), he⟩))) *
              ((C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0, 0, b1, a1), he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by
          simp only [map_mul, map_pow]; ring,
          coeff_C, if_pos rfl]
      · simp only [one_ne_zero, false_and, ↓reduceIte]
        unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_one, pow_zero, mul_one,
          show ∀ (p q r : ContactPoly F), p * (X * q * r) = X * (p * q * r) by intros; ring,
          coeff_X_mul_zero]
      · simp only [one_ne_zero, and_false, ↓reduceIte, true_and]
        unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_one, one_mul,
          show C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩))) *
              ((C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
            X * C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by
          simp only [map_mul, map_pow]; ring,
          coeff_add, coeff_C, if_pos rfl, coeff_X_mul_zero, add_zero]
    rw [hf0]
    have hshift_sum : ∀ (S : Finset (KerDIdx wY W_F 1)) (g : KerDIdx wY W_F 1 → BiPoly F),
        shiftBi x0 y0 (∑ e ∈ S, g e) = ∑ e ∈ S, shiftBi x0 y0 (g e) := by
      intro S g; classical
      induction S using Finset.induction_on with
      | empty => unfold shiftBi; simp
      | insert a S ha ih => rw [Finset.sum_insert ha, shiftBi_add, ih, Finset.sum_insert ha]
    rw [hshift_sum, finset_sum_coeff, finset_sum_coeff]
    have hRHS : (if i % 2 = 0 ∧ j % 2 = 0 then A0 (i / 2) (j / 2)
        else if i % 2 = 0 ∧ j % 2 = 1 then C0 (i / 2) (j / 2)
        else 0) =
        ∑ e : KerDIdx wY W_F 1,
          if i % 2 = 0 ∧ j % 2 = 0 then
            (if e.1.1 = 0 ∧ e.1.2.1 = 0 then
              f_coord e * (Nat.choose e.1.2.2.2 (i / 2) : F) * (x0 ^ 2) ^ (e.1.2.2.2 - i / 2) *
                ((Nat.choose e.1.2.2.1 (j / 2) : F) * (y0 ^ 2) ^ (e.1.2.2.1 - j / 2))
             else if e.1.1 = 0 ∧ e.1.2.1 = 1 then
              f_coord e * y0 * (Nat.choose e.1.2.2.2 (i / 2) : F) * (x0 ^ 2) ^ (e.1.2.2.2 - i / 2) *
                ((Nat.choose e.1.2.2.1 (j / 2) : F) * (y0 ^ 2) ^ (e.1.2.2.1 - j / 2))
             else 0)
          else if i % 2 = 0 ∧ j % 2 = 1 then
            (if e.1.1 = 0 ∧ e.1.2.1 = 1 then
              f_coord e * (Nat.choose e.1.2.2.2 (i / 2) : F) * (x0 ^ 2) ^ (e.1.2.2.2 - i / 2) *
                ((Nat.choose e.1.2.2.1 (j / 2) : F) * (y0 ^ 2) ^ (e.1.2.2.1 - j / 2))
             else 0)
          else 0 := by
      split_ifs <;> [rfl; rfl; simp]
    rw [hRHS]
    apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hmem := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
    have hcases : (k1 = 0 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) ∨ (k1 = 1 ∧ r1 = 0) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- k1 = 0, r1 = 0: shiftBi(c * (X^2)^a1 * (Y^2)^b1)
      simp only [true_and, false_and, zero_ne_one, one_ne_zero, and_false, ↓reduceIte]
      rw [shiftBi_mul, shiftBi_mul, shiftBi_C, shiftBi_pow, shiftBi_C, shiftBi_pow, shiftBi_pow, shiftBi_X]
      simp only [C_comp, pow_comp, X_comp, ← map_pow, hpow_even, hpow_even_Y]
      rw [show C (C (f_coord ⟨(0, 0, b1, a1), he⟩)) *
          C (∑ l ∈ Finset.range (a1 + 1), C ((Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l)) * X ^ (2 * l)) *
          (∑ m ∈ Finset.range (b1 + 1), C (C ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * m)) =
          ∑ m ∈ Finset.range (b1 + 1),
            C (∑ l ∈ Finset.range (a1 + 1),
              C (f_coord ⟨(0, 0, b1, a1), he⟩ * (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
                ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * l)) * X ^ (2 * m) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
        rw [← mul_assoc, ← map_mul, ← map_mul, Finset.mul_sum, Finset.sum_mul]
        congr 1; congr 1; apply Finset.sum_congr rfl; intro l _
        simp only [map_mul]; ring]
      rw [finset_sum_coeff, finset_sum_coeff]
      simp_rw [coeff_C_mul_X_pow]
      split_ifs with hij1 hij2
      · rcases hij1 with ⟨hi, hj⟩
        by_cases hm : j / 2 < b1 + 1
        · rw [Finset.sum_eq_single (j / 2)]
          · rw [if_pos (by omega), finset_sum_coeff]
            by_cases hl : i / 2 < a1 + 1
            · rw [Finset.sum_eq_single (i / 2)]
              · rw [coeff_C_mul_X_pow, if_pos (by omega)]
              · intro l _ hne; rw [coeff_C_mul_X_pow, if_neg (by omega)]
              · intro hnot; exact absurd (Finset.mem_range.mpr hl) hnot
            · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := i / 2) (by omega)]; simp only [Nat.cast_zero, mul_zero, zero_mul]
              apply Finset.sum_eq_zero; intro l hl'
              have := Finset.mem_range.mp hl'
              rw [coeff_C_mul_X_pow, if_neg (by omega)]
          · intro m _ hne; rw [if_neg (by omega), coeff_zero]
          · intro hnot; exact absurd (Finset.mem_range.mpr hm) hnot
        · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := j / 2) (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
          apply Finset.sum_eq_zero; intro m hm'
          have := Finset.mem_range.mp hm'
          rw [if_neg (by omega), coeff_zero]
      · -- j odd => 2*m ≠ j always!
        apply Finset.sum_eq_zero; intro m _
        rw [if_neg (by omega), coeff_zero]
      · -- either i odd or j odd => 0!
        apply Finset.sum_eq_zero; intro m _
        by_cases hmj : j = 2 * m
        · rw [if_pos hmj, finset_sum_coeff]
          apply Finset.sum_eq_zero; intro l _
          rw [coeff_C_mul_X_pow, if_neg (by omega)]
        · rw [if_neg hmj, coeff_zero]
    · -- k1 = 0, r1 = 1: shiftBi(c * Y * (X^2)^a1 * (Y^2)^b1) = c * (y0 + v) * ...
      simp only [true_and, false_and, zero_ne_one, one_ne_zero, and_false, ↓reduceIte]
      rw [shiftBi_mul, shiftBi_mul, shiftBi_mul, shiftBi_C, shiftBi_X, shiftBi_pow, shiftBi_C,
        shiftBi_pow, shiftBi_pow, shiftBi_X]
      simp only [C_comp, pow_comp, X_comp, ← map_pow, hpow_even, hpow_even_Y]
      rw [show C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * (C (C y0) + X) *
          C (∑ l ∈ Finset.range (a1 + 1), C ((Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l)) * X ^ (2 * l)) *
          (∑ m ∈ Finset.range (b1 + 1), C (C ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * m)) =
          (∑ m ∈ Finset.range (b1 + 1),
            C (∑ l ∈ Finset.range (a1 + 1),
              C (f_coord ⟨(0, 1, b1, a1), he⟩ * y0 * (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
                ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * l)) * X ^ (2 * m)) +
          (∑ m ∈ Finset.range (b1 + 1),
            C (∑ l ∈ Finset.range (a1 + 1),
              C (f_coord ⟨(0, 1, b1, a1), he⟩ * (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
                ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * l)) * X ^ (2 * m + 1)) by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m _
        rw [pow_succ, show ∀ p1 p2 p3 p4 : BiPoly F, p1 * (p2 + X) * p3 * (p4 * X ^ (2 * m)) =
          (p1 * p2 * p3 * p4) * X ^ (2 * m) + (p1 * p3 * p4) * (X ^ (2 * m) * X) by intros; ring]
        refine congrArg₂ (· + ·) ?_ ?_
        · congr 1; simp only [← map_mul, Finset.mul_sum, Finset.sum_mul]; congr 1
          apply Finset.sum_congr rfl; intro l _
          simp only [map_mul]; ring
        · congr 1; simp only [← map_mul, Finset.mul_sum, Finset.sum_mul]; congr 1
          apply Finset.sum_congr rfl; intro l _
          simp only [map_mul]; ring]
      rw [coeff_add, coeff_add, finset_sum_coeff, finset_sum_coeff, finset_sum_coeff, finset_sum_coeff]
      simp_rw [coeff_C_mul_X_pow]
      split_ifs with hij1 hij2
      · rcases hij1 with ⟨hi, hj⟩
        have hodd0 : (∑ m ∈ Finset.range (b1 + 1),
            (if j = 2 * m + 1 then ∑ l ∈ Finset.range (a1 + 1),
              C (f_coord ⟨(0, 1, b1, a1), he⟩ * (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
                ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * l) else 0).coeff i) = 0 := by
          apply Finset.sum_eq_zero; intro m _; rw [if_neg (by omega), coeff_zero]
        rw [hodd0, add_zero]
        by_cases hm : j / 2 < b1 + 1
        · rw [Finset.sum_eq_single (j / 2)]
          · rw [if_pos (by omega), finset_sum_coeff]
            by_cases hl : i / 2 < a1 + 1
            · rw [Finset.sum_eq_single (i / 2)]
              · rw [coeff_C_mul_X_pow, if_pos (by omega)]
              · intro l _ hne; rw [coeff_C_mul_X_pow, if_neg (by omega)]
              · intro hnot; exact absurd (Finset.mem_range.mpr hl) hnot
            · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := i / 2) (by omega)]; simp only [Nat.cast_zero, mul_zero, zero_mul]
              apply Finset.sum_eq_zero; intro l hl'
              have := Finset.mem_range.mp hl'; rw [coeff_C_mul_X_pow, if_neg (by omega)]
          · intro m _ hne; rw [if_neg (by omega), coeff_zero]
          · intro hnot; exact absurd (Finset.mem_range.mpr hm) hnot
        · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := j / 2) (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
          apply Finset.sum_eq_zero; intro m hm'
          have := Finset.mem_range.mp hm'; rw [if_neg (by omega), coeff_zero]
      · rcases hij2 with ⟨hi, hj⟩
        have heven0 : (∑ m ∈ Finset.range (b1 + 1),
            (if j = 2 * m then ∑ l ∈ Finset.range (a1 + 1),
              C (f_coord ⟨(0, 1, b1, a1), he⟩ * y0 * (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
                ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * l) else 0).coeff i) = 0 := by
          apply Finset.sum_eq_zero; intro m _; rw [if_neg (by omega), coeff_zero]
        rw [heven0, zero_add]
        by_cases hm : j / 2 < b1 + 1
        · rw [Finset.sum_eq_single (j / 2)]
          · rw [if_pos (by omega), finset_sum_coeff]
            by_cases hl : i / 2 < a1 + 1
            · rw [Finset.sum_eq_single (i / 2)]
              · rw [coeff_C_mul_X_pow, if_pos (by omega)]
              · intro l _ hne; rw [coeff_C_mul_X_pow, if_neg (by omega)]
              · intro hnot; exact absurd (Finset.mem_range.mpr hl) hnot
            · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := i / 2) (by omega)]; simp only [Nat.cast_zero, mul_zero, zero_mul]
              apply Finset.sum_eq_zero; intro l hl'
              have := Finset.mem_range.mp hl'; rw [coeff_C_mul_X_pow, if_neg (by omega)]
          · intro m _ hne; rw [if_neg (by omega), coeff_zero]
          · intro hnot; exact absurd (Finset.mem_range.mpr hm) hnot
        · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := j / 2) (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
          apply Finset.sum_eq_zero; intro m hm'
          have := Finset.mem_range.mp hm'; rw [if_neg (by omega), coeff_zero]
      · -- i is odd => both sums are 0!
        have hi_odd : i % 2 = 1 := by omega
        have h1 : (∑ m ∈ Finset.range (b1 + 1), (if j = 2 * m then ∑ l ∈ Finset.range (a1 + 1),
            C (f_coord ⟨(0, 1, b1, a1), he⟩ * y0 * (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
              ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * l) else 0).coeff i) = 0 := by
          apply Finset.sum_eq_zero; intro m _
          split_ifs
          · rw [finset_sum_coeff]; apply Finset.sum_eq_zero; intro l _; rw [coeff_C_mul_X_pow, if_neg (by omega)]
          · simp
        have h2 : (∑ m ∈ Finset.range (b1 + 1), (if j = 2 * m + 1 then ∑ l ∈ Finset.range (a1 + 1),
            C (f_coord ⟨(0, 1, b1, a1), he⟩ * (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
              ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * l) else 0).coeff i) = 0 := by
          apply Finset.sum_eq_zero; intro m _
          split_ifs
          · rw [finset_sum_coeff]; apply Finset.sum_eq_zero; intro l _; rw [coeff_C_mul_X_pow, if_neg (by omega)]
          · simp
        rw [h1, h2, add_zero]
    · -- k1 = 1, r1 = 0: term is 0!
      simp only [true_and, false_and, zero_ne_one, one_ne_zero, and_false, ↓reduceIte]
      unfold shiftBi; simp
  -- Similarly for f1 = Fpoly.coeff 1!
  have hshift_f1 : ∀ i j, ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff j).coeff i =
      if i % 2 = 0 ∧ j % 2 = 0 then A1 (i / 2) (j / 2)
      else if i % 2 = 1 ∧ j % 2 = 0 then C0 (i / 2) (j / 2)
      else 0 := by
    intro i j
    have hf1 : Fpoly.coeff 1 =
        ∑ e : KerDIdx wY W_F 1,
          if e.1.1 = 1 ∧ e.1.2.1 = 0 then
            C (C (f_coord e)) * (C (X ^ 2) ^ e.1.2.2.2) * (X ^ 2) ^ e.1.2.2.1
          else if e.1.1 = 0 ∧ e.1.2.1 = 1 then
            C (C (f_coord e)) * C X * (C (X ^ 2) ^ e.1.2.2.2) * (X ^ 2) ^ e.1.2.2.1
          else 0 := by
      dsimp [Fpoly]; rw [finset_sum_coeff]
      apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
      have hmem := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
      have hcases : (k1 = 0 ∧ r1 = 0) ∨ (k1 = 1 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [zero_ne_one, false_and, true_and, and_false, ↓reduceIte]
        unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_zero, one_mul, one_mul,
          show C (C (C (f_coord ⟨(0, 0, b1, a1), he⟩))) *
              ((C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0, 0, b1, a1), he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by
          simp only [map_mul, map_pow]; ring,
          coeff_C, if_neg one_ne_zero]
      · simp only [true_and, ↓reduceIte]
        unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_one, pow_zero, mul_one,
          show C (C (C (f_coord ⟨(1, 0, b1, a1), he⟩))) *
              (X * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            X * C (C (C (f_coord ⟨(1, 0, b1, a1), he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by
          simp only [map_mul, map_pow]; ring,
          coeff_X_mul, coeff_C, if_pos rfl]
      · simp only [zero_ne_one, false_and, ↓reduceIte, true_and]
        unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_one, one_mul,
          show C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩))) *
              ((C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
            X * C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by
          simp only [map_mul, map_pow]; ring,
          coeff_add, coeff_C, if_neg one_ne_zero, zero_add, coeff_X_mul, coeff_C, if_pos rfl]
    rw [hf1]
    have hshift_sum : ∀ (S : Finset (KerDIdx wY W_F 1)) (g : KerDIdx wY W_F 1 → BiPoly F),
        shiftBi x0 y0 (∑ e ∈ S, g e) = ∑ e ∈ S, shiftBi x0 y0 (g e) := by
      intro S g; classical
      induction S using Finset.induction_on with
      | empty => unfold shiftBi; simp
      | insert a S ha ih => rw [Finset.sum_insert ha, shiftBi_add, ih, Finset.sum_insert ha]
    rw [hshift_sum, finset_sum_coeff, finset_sum_coeff]
    have hRHS : (if i % 2 = 0 ∧ j % 2 = 0 then A1 (i / 2) (j / 2)
        else if i % 2 = 1 ∧ j % 2 = 0 then C0 (i / 2) (j / 2)
        else 0) =
        ∑ e : KerDIdx wY W_F 1,
          if i % 2 = 0 ∧ j % 2 = 0 then
            (if e.1.1 = 1 ∧ e.1.2.1 = 0 then
              f_coord e * (Nat.choose e.1.2.2.2 (i / 2) : F) * (x0 ^ 2) ^ (e.1.2.2.2 - i / 2) *
                ((Nat.choose e.1.2.2.1 (j / 2) : F) * (y0 ^ 2) ^ (e.1.2.2.1 - j / 2))
             else if e.1.1 = 0 ∧ e.1.2.1 = 1 then
              f_coord e * x0 * (Nat.choose e.1.2.2.2 (i / 2) : F) * (x0 ^ 2) ^ (e.1.2.2.2 - i / 2) *
                ((Nat.choose e.1.2.2.1 (j / 2) : F) * (y0 ^ 2) ^ (e.1.2.2.1 - j / 2))
             else 0)
          else if i % 2 = 1 ∧ j % 2 = 0 then
            (if e.1.1 = 0 ∧ e.1.2.1 = 1 then
              f_coord e * (Nat.choose e.1.2.2.2 (i / 2) : F) * (x0 ^ 2) ^ (e.1.2.2.2 - i / 2) *
                ((Nat.choose e.1.2.2.1 (j / 2) : F) * (y0 ^ 2) ^ (e.1.2.2.1 - j / 2))
             else 0)
          else 0 := by
      split_ifs <;> [rfl; rfl; simp]
    rw [hRHS]
    apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hmem := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
    have hcases : (k1 = 1 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) ∨ (k1 = 0 ∧ r1 = 0) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [true_and, false_and, zero_ne_one, one_ne_zero, and_false, ↓reduceIte]
      rw [shiftBi_mul, shiftBi_mul, shiftBi_C, shiftBi_pow, shiftBi_C, shiftBi_pow, shiftBi_pow, shiftBi_X]
      simp only [C_comp, pow_comp, X_comp, ← map_pow, hpow_even, hpow_even_Y]
      rw [show C (C (f_coord ⟨(1, 0, b1, a1), he⟩)) *
          C (∑ l ∈ Finset.range (a1 + 1), C ((Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l)) * X ^ (2 * l)) *
          (∑ m ∈ Finset.range (b1 + 1), C (C ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * m)) =
          ∑ m ∈ Finset.range (b1 + 1),
            C (∑ l ∈ Finset.range (a1 + 1),
              C (f_coord ⟨(1, 0, b1, a1), he⟩ * (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
                ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * l)) * X ^ (2 * m) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
        rw [← mul_assoc, ← map_mul, ← map_mul, Finset.mul_sum, Finset.sum_mul]
        congr 1; congr 1; apply Finset.sum_congr rfl; intro l _
        simp only [map_mul]; ring]
      rw [finset_sum_coeff, finset_sum_coeff]; simp_rw [coeff_C_mul_X_pow]
      split_ifs with hij1 hij2
      · rcases hij1 with ⟨hi, hj⟩
        by_cases hm : j / 2 < b1 + 1
        · rw [Finset.sum_eq_single (j / 2)]
          · rw [if_pos (by omega), finset_sum_coeff]
            by_cases hl : i / 2 < a1 + 1
            · rw [Finset.sum_eq_single (i / 2)]
              · rw [coeff_C_mul_X_pow, if_pos (by omega)]
              · intro l _ hne; rw [coeff_C_mul_X_pow, if_neg (by omega)]
              · intro hnot; exact absurd (Finset.mem_range.mpr hl) hnot
            · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := i / 2) (by omega)]; simp only [Nat.cast_zero, mul_zero, zero_mul]
              apply Finset.sum_eq_zero; intro l hl'; have := Finset.mem_range.mp hl'; rw [coeff_C_mul_X_pow, if_neg (by omega)]
          · intro m _ hne; rw [if_neg (by omega), coeff_zero]
          · intro hnot; exact absurd (Finset.mem_range.mpr hm) hnot
        · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := j / 2) (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
          apply Finset.sum_eq_zero; intro m hm'; have := Finset.mem_range.mp hm'; rw [if_neg (by omega), coeff_zero]
      · apply Finset.sum_eq_zero; intro m _
        by_cases hmj : j = 2 * m
        · rw [if_pos hmj, finset_sum_coeff]; apply Finset.sum_eq_zero; intro l _; rw [coeff_C_mul_X_pow, if_neg (by omega)]
        · rw [if_neg hmj, coeff_zero]
      · apply Finset.sum_eq_zero; intro m _; rw [if_neg (by omega), coeff_zero]
    · simp only [true_and, false_and, zero_ne_one, one_ne_zero, and_false, ↓reduceIte]
      rw [shiftBi_mul, shiftBi_mul, shiftBi_mul, shiftBi_C, shiftBi_C, shiftBi_pow, shiftBi_C,
        shiftBi_pow, shiftBi_pow, shiftBi_X]
      simp only [C_comp, pow_comp, X_comp, ← map_pow, hpow_even, hpow_even_Y]
      rw [show C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * C (C x0 + X) *
          C (∑ l ∈ Finset.range (a1 + 1), C ((Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l)) * X ^ (2 * l)) *
          (∑ m ∈ Finset.range (b1 + 1), C (C ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * m)) =
          ∑ m ∈ Finset.range (b1 + 1),
            C ((∑ l ∈ Finset.range (a1 + 1),
                C (f_coord ⟨(0, 1, b1, a1), he⟩ * x0 * (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
                  ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * l)) +
               (∑ l ∈ Finset.range (a1 + 1),
                C (f_coord ⟨(0, 1, b1, a1), he⟩ * (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
                  ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * l + 1))) * X ^ (2 * m) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
        rw [← mul_assoc, ← map_mul, ← map_mul, ← map_mul, ← Finset.sum_add_distrib]
        congr 1; congr 1
        rw [show C (f_coord ⟨(0, 1, b1, a1), he⟩) * (C x0 + X) *
          (∑ l ∈ Finset.range (a1 + 1), C ((Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l)) * X ^ (2 * l)) *
          C ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m)) =
          ∑ l ∈ Finset.range (a1 + 1),
            (C (f_coord ⟨(0, 1, b1, a1), he⟩) * (C x0 + X) *
              (C ((Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l)) * X ^ (2 * l)) *
              C ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) by
          rw [Finset.mul_sum, Finset.sum_mul]]
        apply Finset.sum_congr rfl; intro l _
        rw [pow_succ]; simp only [map_mul]; ring]
      rw [finset_sum_coeff, finset_sum_coeff]; simp_rw [coeff_C_mul_X_pow]
      split_ifs with hij1 hij2
      · rcases hij1 with ⟨hi, hj⟩
        by_cases hm : j / 2 < b1 + 1
        · rw [Finset.sum_eq_single (j / 2)]
          · rw [if_pos (by omega), coeff_add, finset_sum_coeff, finset_sum_coeff]
            have hodd0 : (∑ l ∈ Finset.range (a1 + 1), (C (f_coord ⟨(0, 1, b1, a1), he⟩ *
                (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
                ((Nat.choose b1 (j / 2) : F) * (y0 ^ 2) ^ (b1 - j / 2))) * X ^ (2 * l + 1)).coeff i) = 0 := by
              apply Finset.sum_eq_zero; intro l _; rw [coeff_C_mul_X_pow, if_neg (by omega)]
            rw [hodd0, add_zero]
            by_cases hl : i / 2 < a1 + 1
            · rw [Finset.sum_eq_single (i / 2)]
              · rw [coeff_C_mul_X_pow, if_pos (by omega)]
              · intro l _ hne; rw [coeff_C_mul_X_pow, if_neg (by omega)]
              · intro hnot; exact absurd (Finset.mem_range.mpr hl) hnot
            · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := i / 2) (by omega)]; simp only [Nat.cast_zero, mul_zero, zero_mul]
              apply Finset.sum_eq_zero; intro l hl'; have := Finset.mem_range.mp hl'; rw [coeff_C_mul_X_pow, if_neg (by omega)]
          · intro m _ hne; rw [if_neg (by omega), coeff_zero]
          · intro hnot; exact absurd (Finset.mem_range.mpr hm) hnot
        · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := j / 2) (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
          apply Finset.sum_eq_zero; intro m hm'; have := Finset.mem_range.mp hm'; rw [if_neg (by omega), coeff_zero]
      · rcases hij2 with ⟨hi, hj⟩
        by_cases hm : j / 2 < b1 + 1
        · rw [Finset.sum_eq_single (j / 2)]
          · rw [if_pos (by omega), coeff_add, finset_sum_coeff, finset_sum_coeff]
            have heven0 : (∑ l ∈ Finset.range (a1 + 1), (C (f_coord ⟨(0, 1, b1, a1), he⟩ * x0 *
                (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
                ((Nat.choose b1 (j / 2) : F) * (y0 ^ 2) ^ (b1 - j / 2))) * X ^ (2 * l)).coeff i) = 0 := by
              apply Finset.sum_eq_zero; intro l _; rw [coeff_C_mul_X_pow, if_neg (by omega)]
            rw [heven0, zero_add]
            by_cases hl : i / 2 < a1 + 1
            · rw [Finset.sum_eq_single (i / 2)]
              · rw [coeff_C_mul_X_pow, if_pos (by omega)]
              · intro l _ hne; rw [coeff_C_mul_X_pow, if_neg (by omega)]
              · intro hnot; exact absurd (Finset.mem_range.mpr hl) hnot
            · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := i / 2) (by omega)]; simp only [Nat.cast_zero, mul_zero, zero_mul]
              apply Finset.sum_eq_zero; intro l hl'; have := Finset.mem_range.mp hl'; rw [coeff_C_mul_X_pow, if_neg (by omega)]
          · intro m _ hne; rw [if_neg (by omega), coeff_zero]
          · intro hnot; exact absurd (Finset.mem_range.mpr hm) hnot
        · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := j / 2) (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
          apply Finset.sum_eq_zero; intro m hm'; have := Finset.mem_range.mp hm'; rw [if_neg (by omega), coeff_zero]
      · apply Finset.sum_eq_zero; intro m _; rw [if_neg (by omega), coeff_zero]
    · simp only [true_and, false_and, zero_ne_one, one_ne_zero, and_false, ↓reduceIte]
      unfold shiftBi; simp
  -- Finally read off biMultGE (2*k - 1) for both f0 and f1!
  constructor
  · intro i j hij
    rw [hshift_f0]
    split_ifs with h1 h2
    · exact hA0_zero (i / 2) (j / 2) (by omega)
    · exact hC0_zero (i / 2) (j / 2) (by omega)
    · rfl
  · intro i j hij
    rw [hshift_f1]
    split_ifs with h1 h2
    · exact hA1_zero (i / 2) (j / 2) (by omega)
    · exact hC0_zero (i / 2) (j / 2) (by omega)
    · rfl

/-! ### Part 3: Frobenius `f_1 = 0` descent for `deg_R = 2` over a finite field of char 2 -/

/-- Over any finite field `F` of characteristic 2, the Frobenius map `x ↦ x^2` is a ring equivalence,
giving an exact square-root ring homomorphism `frobSqrt : F →+* F` with `(frobSqrt a)^2 = a`! -/
noncomputable def frobEquiv (F : Type*) [Field F] [Fintype F] [CharP F 2] : F ≃+* F :=
  RingEquiv.ofBijective (frobenius F 2)
    ((Fintype.bijective_iff_injective_and_card (frobenius F 2)).mpr
      ⟨frobenius_inj F 2, rfl⟩)

lemma frobEquiv_symm_sq {F : Type*} [Field F] [Fintype F] [CharP F 2] (a : F) :
    ((frobEquiv F).symm a) ^ 2 = a := by
  have h := (frobEquiv F).apply_symm_apply a
  change frobenius F 2 ((frobEquiv F).symm a) = a at h
  rwa [frobenius_def] at h

private lemma coeff_sq_char2 {R : Type*} [CommRing R] (h2R : (2 : R) = 0) (p : Polynomial R) (n : ℕ) :
    (p ^ 2).coeff n = if n % 2 = 0 then (p.coeff (n / 2)) ^ 2 else 0 := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb =>
      have h2 : (2 : Polynomial R) = 0 := by
        rw [show (2 : Polynomial R) = C (2 : R) by
          rw [show (2 : Polynomial R) = 1 + 1 by ring, show (2 : R) = 1 + 1 by ring, map_add, map_one],
          h2R, map_zero]
      rw [show (a + b) ^ 2 = a ^ 2 + b ^ 2 by
        calc (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
          _ = a ^ 2 + b ^ 2 := by rw [h2]; ring]
      rw [coeff_add, ha, hb, coeff_add]
      split_ifs
      · calc (a.coeff (n / 2)) ^ 2 + (b.coeff (n / 2)) ^ 2
            = (a.coeff (n / 2) + b.coeff (n / 2)) ^ 2 - 2 * a.coeff (n / 2) * b.coeff (n / 2) := by ring
          _ = (a.coeff (n / 2) + b.coeff (n / 2)) ^ 2 := by rw [h2R]; ring
      · simp
  | monomial k c =>
      rw [monomial_pow, coeff_monomial, coeff_monomial]
      simp only [Finsupp.single_apply]
      by_cases h1 : n % 2 = 0
      · rw [if_pos h1]
        by_cases h2 : k = n / 2
        · subst h2; simp [show n / 2 * 2 = n by omega]
        · have hk2 : k * 2 ≠ n := by omega
          simp [h2, hk2]
      · rw [if_neg h1]
        have hk2 : k * 2 ≠ n := by omega
        simp [hk2]

/-- **Frobenius `f_1 = 0` descent:**
If `F ∈ ContactPoly (Polynomial Fld)` lies in `ker(D)` with `F.natDegree = 2` and `F.coeff 1 = 0`,
then every exponent of `(X, Y, R)` in `F` is EVEN!
Substituting `Z = w^2` gives `F(X, Y, R, w^2) = H(X, Y, R, w)^2` where:
- `H.natDegree = 1`,
- `2 * wdeg wY H = wdeg wY F`,
- `deg_w(H) ≤ deg_Z(F)`! -/
theorem frobenius_descent_f1_zero {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {wY W_F D_ZF : ℕ} (hwY : 1 ≤ wY)
    (Q : ContactPoly (Polynomial F)) (hDQ : contactDeriv Q = 0)
    (hdeg : Q.natDegree = 2) (hw : wdeg wY Q = W_F) (hQ1 : Q.coeff 1 = 0)
    (hDZ : ∀ k j i, (((Q.coeff k).coeff j).coeff i).natDegree ≤ D_ZF) :
    ∃ H : ContactPoly (Polynomial F),
      H.natDegree = 1 ∧ 2 * wdeg wY H = W_F ∧
      (∀ k j i, (((H.coeff k).coeff j).coeff i).natDegree ≤ D_ZF) ∧
      H ^ 2 = Q.map (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.compRingHom (X ^ 2)))) := by
  -- From D(Q) = 0 and Q.coeff 1 = 0, every nonzero coefficient (k, j, i) has k, j, i ALL EVEN!
  have hall_even : ∀ k j i, (((Q.coeff k).coeff j).coeff i) ≠ 0 →
      k % 2 = 0 ∧ j % 2 = 0 ∧ i % 2 = 0 := by
    intro k j i hne
    have hkle : k ≤ 2 := hdeg ▸ le_natDegree_of_ne_zero (fun h0 => hne (by simp [h0]))
    have hk_even : k % 2 = 0 := by
      by_contra hodd
      have hk1 : k = 1 := by omega
      subst hk1; rw [hQ1] at hne; simp at hne
    have hDentry : ∀ k' j' i',
        ((Q.coeff k').coeff j').coeff (i' + 1) * ((i' + 1 : ℕ) : Polynomial F) +
        (if k' = 0 then 0 else ((Q.coeff (k' - 1)).coeff (j' + 1)).coeff i' * ((j' + 1 : ℕ) : Polynomial F)) = 0 := by
      intro k' j' i'
      have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff j').coeff i') hDQ
      rw [coeff_contactDeriv, coeff_add, coeff_add, coeff_dXBi, coeff_derivative, coeff_zero] at h
      cases k' with
      | zero => simpa using h
      | succ k'' =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_derivative] at h
          rw [show ((j' : Polynomial (Polynomial F)) + 1) = C ((j' : Polynomial F) + 1) by simp, coeff_mul_C] at h
          simpa [Nat.cast_add, Nat.cast_one] using h
    have hmul_odd : ∀ (p : Polynomial F) (n : ℕ), n % 2 = 1 → p * (n : Polynomial F) = p := by
      intro p n hn
      have : (n : Polynomial F) = 1 := by
        rw [show n = 2 * (n / 2) + 1 by omega]; push_cast; simp [CharTwo.two_eq_zero]
      rw [this, mul_one]
    have hmul_even : ∀ (p : Polynomial F) (n : ℕ), n % 2 = 0 → p * (n : Polynomial F) = 0 := by
      intro p n hn
      have : (n : Polynomial F) = 0 := by
        rw [show n = 2 * (n / 2) by omega]; push_cast; simp [CharTwo.two_eq_zero]
      rw [this, mul_zero]
    have hi_even : i % 2 = 0 := by
      by_contra hodd
      have hi1 : i % 2 = 1 := by omega
      have h := hDentry k j (i - 1)
      rw [show i - 1 + 1 = i by omega, hmul_odd _ _ hi1] at h
      rcases (show k = 0 ∨ k = 2 by omega) with rfl | rfl
      · simp at h; exact hne h
      · simp [hQ1] at h; exact hne h
    have hj_even : j % 2 = 0 := by
      by_contra hodd
      have hj1 : j % 2 = 1 := by omega
      have h := hDentry (k + 1) (j - 1) i
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, show j - 1 + 1 = j by omega] at h
      rw [hmul_odd _ _ hj1] at h
      rcases (show k = 0 ∨ k = 2 by omega) with rfl | rfl
      · simp [hQ1] at h; exact hne h
      · have hQ3 : Q.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        simp [hQ3] at h; exact hne h
    exact ⟨hk_even, hj_even, hi_even⟩
  -- Define H directly by halving every exponent (2k, 2j, 2i) and applying frobEquiv.symm to each F-coefficient!
  let sqrtPoly (p : Polynomial F) : Polynomial F := p.map (frobEquiv F).symm.toRingHom
  have hsqrt_sq : ∀ p : Polynomial F, (sqrtPoly p) ^ 2 = p.comp (X ^ 2) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add a b ha hb =>
        have h2 : (2 : Polynomial F) = 0 := by simp [CharTwo.two_eq_zero]
        dsimp [sqrtPoly] at ha hb ⊢
        rw [Polynomial.map_add, add_comp, ← ha, ← hb]
        calc (a.map _ + b.map _) ^ 2 = a.map _ ^ 2 + 2 * a.map _ * b.map _ + b.map _ ^ 2 := by ring
          _ = a.map _ ^ 2 + b.map _ ^ 2 := by rw [h2]; ring
    | monomial n c =>
        dsimp [sqrtPoly]
        rw [map_monomial, monomial_comp, monomial_pow, RingHom.coe_coe, frobEquiv_symm_sq,
          ← pow_mul, mul_comm 2 n, C_mul_X_pow_eq_monomial]
  let H : ContactPoly (Polynomial F) :=
    ∑ k ∈ Finset.range 2,
      monomial k
        (∑ j ∈ Finset.range ((Q.coeff (2 * k)).natDegree / 2 + 1),
          monomial j
            (∑ i ∈ Finset.range (((Q.coeff (2 * k)).coeff (2 * j)).natDegree / 2 + 1),
              monomial i (sqrtPoly (((Q.coeff (2 * k)).coeff (2 * j)).coeff (2 * i)))))
  have hH_coeff : ∀ k j i, ((H.coeff k).coeff j).coeff i =
      if k < 2 then sqrtPoly (((Q.coeff (2 * k)).coeff (2 * j)).coeff (2 * i)) else 0 := by
    intro k j i
    dsimp [H]; rw [finset_sum_coeff, finset_sum_coeff, finset_sum_coeff]
    by_cases hk : k < 2
    · rw [if_pos hk, Finset.sum_eq_single k]
      · simp only [coeff_monomial, Finsupp.single_apply, ↓reduceIte]
        rw [finset_sum_coeff, finset_sum_coeff]
        by_cases hj : j < (Q.coeff (2 * k)).natDegree / 2 + 1
        · rw [Finset.sum_eq_single j]
          · simp only [coeff_monomial, Finsupp.single_apply, ↓reduceIte]
            rw [finset_sum_coeff]
            by_cases hi : i < ((Q.coeff (2 * k)).coeff (2 * j)).natDegree / 2 + 1
            · rw [Finset.sum_eq_single i]
              · simp only [coeff_monomial, Finsupp.single_apply, ↓reduceIte]
              · intro i' _ hne; simp only [coeff_monomial, Finsupp.single_apply, if_neg hne]
              · intro hnot; exact absurd (Finset.mem_range.mpr hi) hnot
            · have h0 : ((Q.coeff (2 * k)).coeff (2 * j)).coeff (2 * i) = 0 :=
                coeff_eq_zero_of_natDegree_lt (by omega)
              rw [h0]; simp only [sqrtPoly, Polynomial.map_zero]
              apply Finset.sum_eq_zero; intro i' hi'
              have := Finset.mem_range.mp hi'; simp only [coeff_monomial, Finsupp.single_apply, if_neg (show i' ≠ i by omega)]
          · intro j' _ hne; simp only [coeff_monomial, Finsupp.single_apply, if_neg hne, coeff_zero]
          · intro hnot; exact absurd (Finset.mem_range.mpr hj) hnot
        · have h0 : (Q.coeff (2 * k)).coeff (2 * j) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
          rw [h0, coeff_zero]; simp only [sqrtPoly, Polynomial.map_zero]
          apply Finset.sum_eq_zero; intro j' hj'
          have := Finset.mem_range.mp hj'; simp only [coeff_monomial, Finsupp.single_apply, if_neg (show j' ≠ j by omega), coeff_zero]
      · intro k' _ hne; simp only [coeff_monomial, Finsupp.single_apply, if_neg hne, coeff_zero]
      · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
    · rw [if_neg hk]
      apply Finset.sum_eq_zero; intro k' hk'
      have := Finset.mem_range.mp hk'; simp only [coeff_monomial, Finsupp.single_apply, if_neg (show k' ≠ k by omega), coeff_zero]
  -- Prove H^2 = Q(Z ↦ w^2) entry-by-entry using Frobenius additivity in char 2!
  have hH_sq : H ^ 2 = Q.map (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.compRingHom (X ^ 2)))) := by
    have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
    have h2P1 : (2 : Polynomial F) = 0 := by
      rw [show (2 : Polynomial F) = C (2 : F) by
        rw [show (2 : Polynomial F) = 1 + 1 by ring, show (2 : F) = 1 + 1 by ring, map_add, map_one],
        h2F, map_zero]
    have h2P2 : (2 : Polynomial (Polynomial F)) = 0 := by
      rw [show (2 : Polynomial (Polynomial F)) = C (2 : Polynomial F) by
        rw [show (2 : Polynomial (Polynomial F)) = 1 + 1 by ring, show (2 : Polynomial F) = 1 + 1 by ring, map_add, map_one],
        h2P1, map_zero]
    have h2P3 : (2 : BiPoly (Polynomial F)) = 0 := by
      rw [show (2 : BiPoly (Polynomial F)) = C (2 : Polynomial (Polynomial F)) by
        rw [show (2 : BiPoly (Polynomial F)) = 1 + 1 by ring, show (2 : Polynomial (Polynomial F)) = 1 + 1 by ring, map_add, map_one],
        h2P2, map_zero]
    refine Polynomial.ext fun k => Polynomial.ext fun j => Polynomial.ext fun i => ?_
    simp only [coe_mapRingHom, coeff_map, coe_compRingHom]
    rw [coeff_sq_char2 h2P3 H k]
    split_ifs with hk
    · rw [coeff_sq_char2 h2P2 (H.coeff (k / 2)) j]
      split_ifs with hj
      · rw [coeff_sq_char2 h2P1 ((H.coeff (k / 2)).coeff (j / 2)) i]
        split_ifs with hi
        · rw [hH_coeff]
          by_cases hk2 : k / 2 < 2
          · rw [if_pos hk2, hsqrt_sq, show 2 * (k / 2) = k by omega, show 2 * (j / 2) = j by omega,
              show 2 * (i / 2) = i by omega]
          · rw [if_neg hk2, zero_pow (by omega)]
            have h0 : Q.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
            rw [h0, coeff_zero, coeff_zero, zero_comp]
        · symm
          by_contra hne
          have hqne : ((Q.coeff k).coeff j).coeff i ≠ 0 := fun h0 => hne (by rw [h0, zero_comp])
          exact hi (hall_even k j i hqne).2.2
      · simp only [coeff_zero]; symm
        by_contra hne
        have hqne : ((Q.coeff k).coeff j).coeff i ≠ 0 := fun h0 => hne (by rw [h0, zero_comp])
        exact hj (hall_even k j i hqne).2.1
    · simp only [coeff_zero]; symm
      by_contra hne
      have hqne : ((Q.coeff k).coeff j).coeff i ≠ 0 := fun h0 => hne (by rw [h0, zero_comp])
      exact hk (hall_even k j i hqne).1
  refine ⟨H, ?_, ?_, ?_, hH_sq⟩
  · -- H.natDegree = 1
    apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]; intro k hk
      refine Polynomial.ext fun j => Polynomial.ext fun i => ?_
      rw [hH_coeff, if_neg (by omega), coeff_zero, coeff_zero]
    · apply le_natDegree_of_ne_zero
      intro h0
      have hQ2 : Q.coeff 2 ≠ 0 := hdeg ▸ leadingCoeff_ne_zero.mpr (by intro hQ0; rw [hQ0, natDegree_zero] at hdeg; omega)
      -- Pick a nonzero entry (2, j, i) of Q.coeff 2; then (1, j/2, i/2) of H is nonzero!
      obtain ⟨j, hj⟩ : ∃ j, (Q.coeff 2).coeff j ≠ 0 := ⟨(Q.coeff 2).natDegree, leadingCoeff_ne_zero.mpr hQ2⟩
      obtain ⟨i, hi⟩ : ∃ i, ((Q.coeff 2).coeff j).coeff i ≠ 0 := ⟨((Q.coeff 2).coeff j).natDegree, leadingCoeff_ne_zero.mpr hj⟩
      have hev := hall_even 2 j i hi
      have h1 := congrArg (fun p : BiPoly (Polynomial F) => (p.coeff (j / 2)).coeff (i / 2)) h0
      rw [hH_coeff, if_pos (by omega), coeff_zero, coeff_zero, show 2 * 1 = 2 by rfl,
        show 2 * (j / 2) = j by omega, show 2 * (i / 2) = i by omega] at h1
      have hsq := hsqrt_sq (((Q.coeff 2).coeff j).coeff i)
      rw [h1, zero_pow (by omega)] at hsq
      -- p.comp (X^2) = 0 => p = 0!
      apply hi
      ext n
      have hc := congrArg (fun p : Polynomial F => p.coeff (2 * n)) hsq.symm
      rw [coeff_zero] at hc
      have hcomp2 : ∀ (p : Polynomial F) (n : ℕ), (p.comp (X ^ 2)).coeff (2 * n) = p.coeff n := by
        intro p n
        induction p using Polynomial.induction_on' with
        | add a b ha hb => rw [add_comp, coeff_add, coeff_add, ha, hb]
        | monomial m c =>
            rw [monomial_comp, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial, coeff_monomial]
            by_cases hmn : m = n
            · subst hmn; simp [Finsupp.single_apply]
            · simp [Finsupp.single_apply, hmn, show 2 * m ≠ 2 * n by omega]
      rw [hcomp2] at hc; exact hc
  · -- 2 * wdeg wY H = W_F (from wdeg (H^2) = 2 * wdeg H and wdeg (Q(Z ↦ w^2)) = wdeg Q = W_F!)
    have hHne : H ≠ 0 := by
      intro h0; rw [h0, zero_pow (by omega)] at hH_sq
      -- Q.coeff 2 ≠ 0 contradicts hH_sq
      have hQ2 : Q.coeff 2 ≠ 0 := hdeg ▸ leadingCoeff_ne_zero.mpr (by intro hQ0; rw [hQ0, natDegree_zero] at hdeg; omega)
      obtain ⟨j, hj⟩ : ∃ j, (Q.coeff 2).coeff j ≠ 0 := ⟨(Q.coeff 2).natDegree, leadingCoeff_ne_zero.mpr hQ2⟩
      obtain ⟨i, hi⟩ : ∃ i, ((Q.coeff 2).coeff j).coeff i ≠ 0 := ⟨((Q.coeff 2).coeff j).natDegree, leadingCoeff_ne_zero.mpr hj⟩
      have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff 2).coeff j).coeff i) hH_sq
      simp only [coe_mapRingHom, coeff_map, coe_compRingHom, coeff_zero] at h
      apply hi; ext n
      have hc := congrArg (fun p : Polynomial F => p.coeff (2 * n)) h.symm
      rw [coeff_zero] at hc
      have hcomp2 : ∀ (p : Polynomial F) (n : ℕ), (p.comp (X ^ 2)).coeff (2 * n) = p.coeff n := by
        intro p n
        induction p using Polynomial.induction_on' with
        | add a b ha hb => rw [add_comp, coeff_add, coeff_add, ha, hb]
        | monomial m c =>
            rw [monomial_comp, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial, coeff_monomial]
            by_cases hmn : m = n
            · subst hmn; simp [Finsupp.single_apply]
            · simp [Finsupp.single_apply, hmn, show 2 * m ≠ 2 * n by omega]
      rw [hcomp2] at hc; exact hc
    have hmul : wdeg wY (H ^ 2) = 2 * wdeg wY H := by
      rw [sq, wdeg_mul wY hHne hHne]; omega
    rw [← hmul, hH_sq, ← hw]
    -- Show wdeg of Q(Z ↦ w^2) = wdeg Q since comp (X^2) is injective!
    have hinj : ∀ p : Polynomial F, p.comp (X ^ 2) = 0 ↔ p = 0 := by
      intro p; constructor
      · intro h0; ext n
        have hc := congrArg (fun q : Polynomial F => q.coeff (2 * n)) h0
        rw [coeff_zero] at hc
        have hcomp2 : ∀ (q : Polynomial F) (n : ℕ), (q.comp (X ^ 2)).coeff (2 * n) = q.coeff n := by
          intro q n
          induction q using Polynomial.induction_on' with
          | add a b ha hb => rw [add_comp, coeff_add, coeff_add, ha, hb]
          | monomial m c =>
              rw [monomial_comp, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial, coeff_monomial]
              by_cases hmn : m = n
              · subst hmn; simp [Finsupp.single_apply]
              · simp [Finsupp.single_apply, hmn, show 2 * m ≠ 2 * n by omega]
        rw [hcomp2] at hc; exact hc
      · rintro rfl; simp
    apply le_antisymm
    · rw [wdeg_le_iff]; intro k j i hnz
      simp only [coe_mapRingHom, coeff_map, coe_compRingHom] at hnz
      exact (wdeg_le_iff wY (wdeg wY Q) Q).mp le_rfl k j i (mt (hinj _).mpr hnz)
    · rw [wdeg_le_iff]; intro k j i hnz
      have hnz' : (((Q.map (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.compRingHom (X ^ 2))))).coeff k).coeff j).coeff i ≠ 0 := by
        simp only [coe_mapRingHom, coeff_map, coe_compRingHom]
        exact mt (hinj _).mp hnz
      exact (wdeg_le_iff wY _ _).mp le_rfl k j i hnz'
  · -- deg_w(H) ≤ D_ZF
    intro k j i
    rw [hH_coeff]
    split_ifs
    · exact natDegree_map_le.trans (hDZ (2 * k) (2 * j) (2 * i))
    · simp

end KerDLocalOrders

end B6401KerDOrders
end ProximityPrize.SubmissionBinaryLower
