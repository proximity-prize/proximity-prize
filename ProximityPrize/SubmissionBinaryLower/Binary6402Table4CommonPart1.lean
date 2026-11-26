import ProximityPrize.SubmissionBinaryLower.Binary6402Table4CommonPart0
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

lemma quad_splits_algClosed (g0 g1 g2 : K) (hg2 : g2 ≠ 0) :
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

lemma res_5_4_eq_5_2_of_inj {K : Type*} [Field K] [CharP K 2]
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

lemma exists_poly_syzygy_of_det_zero {K : Type*} [Field K]
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

lemma isCoprime_of_forall_dvd_isUnit_poly {K : Type*} [Field K] [DecidableEq K]
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

end B6402Table4Common
end ProximityPrize.SubmissionBinaryLower
