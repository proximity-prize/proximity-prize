import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.B6401KerDOrders
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 4000000

/-!
# Characteristic-2 `ker(D)` Resultant Identities, `deg_R = 2` Local Orders, and Univariate/Bivariate Sum Bounds

Provides the algebraic engine behind Tables 1, 2, and 3:
1. `resultant_expand2` & `resultant_expand2_even`: exact char-2 identity
   `Res_Y^{(df, 2*dg2)}(Pe(Y^2) + Y * Po(Y^2), G(Y^2)) = Res_V^{(df, dg2)}(Pe(V)^2 + V * Po(V)^2, G(V))`
   and its even specialization `Res_Y^{(2*df2, 2*dg2)}(Pe(Y^2), G(Y^2)) = (Res_V^{(df2, dg2)}(Pe, G))^2`.
2. `kerD1_weighted_decomp` & `kerD1_resY_ord`: exact `(4k + 2)`-weighted decomposition of `deg_R = 1`
   elements of `ker(D)` yielding `(X - C x0) ^ (resOrdWeighted dp (4k+2) (d1/2) (2k-1) 2 - d1)` divisibility
   of `lc_Y(f1)^(dp - deg_Y f0) * Res_Y(f0, f1)`.
3. `kerD2_local_ords`: for `deg_R = 2` `F = f_0 + f_1 R + f_2 R^2 ∈ K_{W_F}(2)` with `twOrdGE (localShift F) k`:
   - `biMultGE x0 y0 f_0 (2 * k - 2)`, `biMultGE x0 y0 f_1 (2 * k - 1)`, `biMultGE x0 y0 f_2 (2 * k - 2)`,
   - exact `(4k + 4)`-weighted decomposition `s^2 f_0 + s v f_1 + v^2 f_2 = Pe(s, v^2) + v * Po(s, v^2)`
     with `weightedOrdGE 2 (2 * k + 2) Pe`, `weightedOrdGE 2 (2 * k + 1) Po`, and
     `weightedOrdGE 2 (4 * k + 4) (Pe^2 + V * Po^2)`!
4. `kerD2_resY_f0_g_ord` & `kerD2_resY_f0_g_2A_ord`: exact `v_ker` and `v_pln` divisibility of
   `lc_Y(g)^(dStar - deg_Y f0) * Res_Y(f0, g)` for ANY divisor `g ∈ F[X, Y^2]` of `(f1, f2)` (both general
   and char-2 `2A` `g = q(X) * g_e(X^2, Y^2)`!).
5. Global sum-of-orders and degree bounds (`sum_ord_univariate_le`, `sum_biMultGE_eval_le`,
   `pow_dvd_leadingCoeff_of_biMultGE`, `natDegree_leadingCoeff_le_wdegBi`, `natDegree_resultant_le_wdegBi`).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401KerD2

open Polynomial B6401ContactKerD B6401QuotInterp B6401ResultantOrd B6401KerDOrders
open scoped BigOperators
local notation (priority := high) "X" => Polynomial.X

/-! ### Part 1: Exact Char-2 Resultant `expand 2` Identities -/

section ResultantExpand2

private lemma expand_two_X_sub_C_sq {L : Type*} [Field L] [CharP L 2] (r : L) :
    Polynomial.expand L 2 (X - C (r ^ 2)) = (X - C r) ^ 2 := by
  have h2 : (2 : Polynomial L) = 0 := by
    rw [show (2 : Polynomial L) = C (2 : L) by
      rw [show (2 : Polynomial L) = 1 + 1 by ring, show (2 : L) = 1 + 1 by ring, map_add, map_one],
      CharTwo.two_eq_zero, map_zero]
  rw [map_sub, Polynomial.expand_X, Polynomial.expand_C]
  calc X ^ 2 - C (r ^ 2) = X ^ 2 - 2 * X * C r + C (r ^ 2) := by
        rw [h2, zero_mul, zero_mul, sub_zero, CharTwo.sub_eq_add]
    _ = (X - C r) ^ 2 := by rw [map_pow]; ring

private lemma sq_add_char2 {R : Type*} [CommRing R] [CharP R 2] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  calc (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
    _ = a ^ 2 + b ^ 2 := by rw [h2]; ring

private lemma natDegree_expand_two_le {R : Type*} [CommRing R] (p : R[X]) :
    (Polynomial.expand R 2 p).natDegree ≤ 2 * p.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [Polynomial.coeff_expand (by norm_num : 0 < 2)]
  split_ifs with hdiv
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · rfl

private lemma natDegree_expand_two_eq {R : Type*} [CommRing R] [IsDomain R] (p : R[X]) :
    (Polynomial.expand R 2 p).natDegree = 2 * p.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [Polynomial.natDegree_expand, mul_comm]

/-- **Exact Char-2 `expand 2` Resultant Identity:**
Over ANY integral domain `R` of characteristic 2, for `Pe, Po, G ∈ R[X]` with
`2 * Pe.natDegree ≤ df`, `2 * Po.natDegree + 1 ≤ df`, `G.natDegree = dg2`:
`Res_Y^{(df, 2*dg2)}(Pe(Y^2) + Y * Po(Y^2), G(Y^2)) = Res_V^{(df, dg2)}(Pe(V)^2 + V * Po(V)^2, G(V))`! -/
theorem resultant_expand2 {R : Type*} [CommRing R] [IsDomain R] [CharP R 2]
    (Pe Po G : R[X]) (df dg2 : ℕ)
    (hPe : 2 * Pe.natDegree ≤ df) (hPo : 2 * Po.natDegree + 1 ≤ df) (hG : G.natDegree = dg2) :
    Polynomial.resultant (Polynomial.expand R 2 Pe + X * Polynomial.expand R 2 Po)
        (Polynomial.expand R 2 G) df (2 * dg2) =
      Polynomial.resultant (Pe ^ 2 + X * Po ^ 2) G df dg2 := by
  by_cases hG0 : G = 0
  · subst hG0; subst hG; simp
  let K := FractionRing R
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  haveI : CharP K 2 := charP_of_injective_ringHom hRK 2
  let GK : K[X] := G.map (algebraMap R K)
  let L := (GK * Polynomial.expand K 2 GK).SplittingField
  have hKL : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  haveI : CharP L 2 := charP_of_injective_ringHom hKL 2
  let φ : R →+* L := (algebraMap K L).comp (algebraMap R K)
  have hφ : Function.Injective φ := hKL.comp hRK
  apply hφ
  rw [← Polynomial.resultant_map_map, ← Polynomial.resultant_map_map]
  rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_expand, Polynomial.map_expand, Polynomial.map_expand]
  set pe : L[X] := Pe.map φ
  set po : L[X] := Po.map φ
  set g : L[X] := G.map φ
  have hg_ne : g ≠ 0 := (Polynomial.map_ne_zero_iff hφ).mpr hG0
  have hg_deg : g.natDegree = dg2 := by
    dsimp [g]; rw [Polynomial.natDegree_map_eq_of_injective hφ, hG]
  have hpe_deg : 2 * pe.natDegree ≤ df := by
    dsimp [pe]; rw [Polynomial.natDegree_map_eq_of_injective hφ]; exact hPe
  have hpo_deg : 2 * po.natDegree + 1 ≤ df := by
    dsimp [po]; rw [Polynomial.natDegree_map_eq_of_injective hφ]; exact hPo
  set f : L[X] := Polynomial.expand L 2 pe + X * Polynomial.expand L 2 po
  set H : L[X] := pe ^ 2 + X * po ^ 2
  have hf_deg : f.natDegree ≤ df := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_expand_two_le pe).trans hpe_deg
    · by_cases hpo0 : po = 0
      · simp [hpo0]
      · refine (Polynomial.natDegree_mul_le).trans ?_
        have h1 : (X : L[X]).natDegree = 1 := Polynomial.natDegree_X
        have h2 := natDegree_expand_two_le po
        omega
  have hH_deg : H.natDegree ≤ df := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_pow_le).trans hpe_deg
    · by_cases hpo0 : po = 0
      · simp [hpo0]
      · refine (Polynomial.natDegree_mul_le).trans ?_
        have h1 : (X : L[X]).natDegree = 1 := Polynomial.natDegree_X
        have h2 : (po ^ 2).natDegree ≤ 2 * po.natDegree := Polynomial.natDegree_pow_le
        omega
  -- Both g and expand L 2 g split over L!
  have hprod_splits : (g * Polynomial.expand L 2 g).Splits := by
    have hs := Polynomial.SplittingField.splits (GK * Polynomial.expand K 2 GK)
    have heq : (GK * Polynomial.expand K 2 GK).map (algebraMap K L) = g * Polynomial.expand L 2 g := by
      simp [GK, g, φ, Polynomial.map_mul, Polynomial.map_expand, Polynomial.map_map]
    rwa [heq] at hs
  have hg_splits : g.Splits := hprod_splits.of_dvd (mul_ne_zero hg_ne (by
    intro h0; exact hg_ne (Polynomial.expand_injective (by norm_num : 0 < 2) (by simpa using h0)))) (dvd_mul_right _ _)
  have hg2_splits : (Polynomial.expand L 2 g).Splits := hprod_splits.of_dvd (mul_ne_zero hg_ne (by
    intro h0; exact hg_ne (Polynomial.expand_injective (by norm_num : 0 < 2) (by simpa using h0)))) (dvd_mul_left _ _)
  -- Every root α of g has a square root r ∈ L!
  have hsqrt : ∀ α ∈ g.roots, ∃ r : L, r ^ 2 = α := by
    intro α hα
    have hdvd1 : X - C α ∣ g := Polynomial.dvd_iff_isRoot.mpr (Polynomial.isRoot_of_mem_roots hα)
    have hdvd2 : X ^ 2 - C α ∣ Polynomial.expand L 2 g := by
      rcases hdvd1 with ⟨q, hq⟩
      refine ⟨Polynomial.expand L 2 q, ?_⟩
      rw [hq, map_mul, map_sub, Polynomial.expand_X, Polynomial.expand_C]
    have hsp : (X ^ 2 - C α).Splits := hg2_splits.of_dvd (by
      intro h0; exact hg_ne (Polynomial.expand_injective (by norm_num : 0 < 2) (by simpa using h0))) hdvd2
    have hdeg2 : (X ^ 2 - C α : L[X]).degree ≠ 0 := by
      have hnd : (X ^ 2 - C α : L[X]).natDegree = 2 := by
        rw [sub_eq_add_neg, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
        · exact Polynomial.natDegree_X_pow 2
        · simp [Polynomial.natDegree_X_pow]
      intro h0; have := Polynomial.natDegree_eq_of_degree_eq_some (n := 0) h0; omega
    obtain ⟨r, hr⟩ := hsp.exists_eval_eq_zero hdeg2
    refine ⟨r, ?_⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at hr
    exact hr
  -- Induction on any multiset M of roots admitting square roots in L!
  have hmult : ∀ (M : Multiset L), (∀ α ∈ M, ∃ r : L, r ^ 2 = α) →
      Polynomial.resultant f (Polynomial.expand L 2 (M.map fun α => X - C α).prod) df (2 * M.card) =
        Polynomial.resultant H (M.map fun α => X - C α).prod df M.card := by
    intro M
    induction M using Multiset.induction_on with
    | empty =>
        intro _; simp
    | cons α M ih =>
        intro hM
        obtain ⟨r, hr⟩ := hM α (Multiset.mem_cons_self _ _)
        have hM' : ∀ β ∈ M, ∃ r' : L, r' ^ 2 = β := fun β hβ => hM β (Multiset.mem_cons_of_mem hβ)
        set Q : L[X] := (M.map fun β => X - C β).prod
        have hQ_monic : Q.Monic := Polynomial.monic_multiset_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)
        have hQ_deg : Q.natDegree = M.card := by
          dsimp [Q]; rw [Polynomial.natDegree_multiset_prod_of_monic _ (fun p hp => by
            rcases Multiset.mem_map.mp hp with ⟨a, _, rfl⟩; exact Polynomial.monic_X_sub_C a)]
          simp [Polynomial.natDegree_X_sub_C]
        have hQ2_deg : (Polynomial.expand L 2 Q).natDegree = 2 * M.card := by
          rw [natDegree_expand_two_eq, hQ_deg]
        have hL1_deg : (X - C α : L[X]).natDegree = 1 := Polynomial.natDegree_X_sub_C α
        have hL2_deg : (Polynomial.expand L 2 (X - C α)).natDegree = 2 := by
          rw [natDegree_expand_two_eq, hL1_deg]
        rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, map_mul]
        have h2card : 2 * (M.card + 1) = (Polynomial.expand L 2 (X - C α)).natDegree + (Polynomial.expand L 2 Q).natDegree := by
          rw [hL2_deg, hQ2_deg]; omega
        have h1card : M.card + 1 = (X - C α : L[X]).natDegree + Q.natDegree := by
          rw [hL1_deg, hQ_deg]; omega
        rw [h2card, Polynomial.resultant_mul_right f _ _ df hf_deg, hL2_deg, hQ2_deg,
          h1card, Polynomial.resultant_mul_right H _ _ df hH_deg, hL1_deg, hQ_deg, ih hM']
        congr 1
        -- 1-factor identity: Res_Y^{(df, 2)}(f, (Y - r)^2) = Res_V^{(df, 1)}(H, V - r^2)!
        rw [← hr, expand_two_X_sub_C_sq r,
          Polynomial.resultant_X_sub_C_pow_right f r df 2 hf_deg,
          Polynomial.resultant_X_sub_C_right H df (r ^ 2) hH_deg]
        dsimp [f, H]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow,
          Polynomial.expand_eval, sq_add_char2, mul_pow, CharTwo.neg_eq, one_pow, one_mul]
  -- Factor g = C g.leadingCoeff * ∏ (X - C α) and finish!
  set S := g.roots
  have hg_fac : g = C g.leadingCoeff * (S.map fun α => X - C α).prod := hg_splits.eq_prod_roots
  have hg_card : S.card = dg2 := by rw [← hg_deg]; exact hg_splits.natDegree_eq_card_roots.symm
  rw [← hg_card]
  conv_lhs => rw [hg_fac, map_mul, Polynomial.expand_C]
  conv_rhs => rw [hg_fac]
  rw [Polynomial.resultant_C_mul_right, Polynomial.resultant_C_mul_right, hmult S hsqrt]

/-- **Even Char-2 `expand 2` Resultant Identity (for Table 3 `2A`):**
`Res_Y^{(2*df2, 2*dg2)}(Pe(Y^2), G(Y^2)) = (Res_V^{(df2, dg2)}(Pe, G))^2`! -/
theorem resultant_expand2_even {R : Type*} [CommRing R] [IsDomain R] [CharP R 2]
    (Pe G : R[X]) (df2 dg2 : ℕ)
    (hPe : Pe.natDegree ≤ df2) (hG : G.natDegree = dg2) :
    Polynomial.resultant (Polynomial.expand R 2 Pe) (Polynomial.expand R 2 G) (2 * df2) (2 * dg2) =
      (Polynomial.resultant Pe G df2 dg2) ^ 2 := by
  by_cases hdf2 : df2 = 0
  · subst hdf2
    have hPe0 : Pe = C (Pe.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hPe
    rw [hPe0, Polynomial.expand_C, mul_zero,
      Polynomial.resultant_C_left (Polynomial.expand R 2 G) 0 (2 * dg2) (Pe.coeff 0),
      Polynomial.resultant_C_left G 0 dg2 (Pe.coeff 0)]
    simp [pow_mul']
  · have h1 := resultant_expand2 Pe 0 G (2 * df2) dg2 (by omega) (by simp; omega) hG
    have h0e : Polynomial.expand R 2 (0 : R[X]) = 0 := map_zero _
    have h02 : (0 : R[X]) ^ 2 = 0 := zero_pow (by norm_num)
    rw [h0e, h02, mul_zero, add_zero, add_zero] at h1
    rw [h1]
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hPe
    have h2df2 : 2 * df2 = (Pe.natDegree + Pe.natDegree) + 2 * c := by omega
    rw [sq, h2df2, Polynomial.resultant_add_left_deg (Pe * Pe) G (Pe.natDegree + Pe.natDegree) dg2 (2 * c)
        Polynomial.natDegree_mul_le,
      Polynomial.resultant_mul_left Pe Pe G dg2 (le_of_eq hG),
      hc, Polynomial.resultant_add_left_deg Pe G Pe.natDegree dg2 c le_rfl]
    ring

end ResultantExpand2

/-! ### Part 2: Weighted `ker(D)` Decompositions (`deg_R = 1` & `deg_R = 2`) -/

section KerDLocalDecomp

variable {F : Type*} [Field F] [CharP F 2]

private lemma h2_poly : (2 : Polynomial F) = 0 := by
  rw [show (2 : Polynomial F) = C (2 : F) by
    rw [show (2 : Polynomial F) = 1 + 1 by ring, show (2 : F) = 1 + 1 by ring, map_add, map_one],
    CharTwo.two_eq_zero, map_zero]

private lemma h2_bi : (2 : BiPoly F) = 0 := by
  rw [show (2 : BiPoly F) = C (2 : Polynomial F) by
    rw [show (2 : BiPoly F) = 1 + 1 by ring, show (2 : Polynomial F) = 1 + 1 by ring, map_add, map_one],
    h2_poly, map_zero]

private lemma add_sq_poly (a b : Polynomial F) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  calc (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
    _ = a ^ 2 + b ^ 2 := by rw [h2_poly]; ring

private lemma add_sq_bi (a b : BiPoly F) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  calc (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
    _ = a ^ 2 + b ^ 2 := by rw [h2_bi]; ring

private lemma shift_even_X (c : F) (n : ℕ) :
    ((C c + X : Polynomial F) ^ 2) ^ n =
      ∑ l ∈ Finset.range (n + 1), C ((Nat.choose n l : F) * (c ^ 2) ^ (n - l)) * X ^ (2 * l) := by
  have hsq : (C c + X : Polynomial F) ^ 2 = C (c ^ 2) + X ^ 2 := by
    rw [add_sq_poly, ← map_pow]
  rw [hsq, add_comm, add_pow]
  apply Finset.sum_congr rfl; intro l _
  rw [← pow_mul, ← map_pow, mul_assoc,
    show C ((c ^ 2) ^ (n - l)) * (Nat.choose n l : Polynomial F) =
      C ((Nat.choose n l : F) * (c ^ 2) ^ (n - l)) by simp [mul_comm], mul_comm]

private lemma shift_even_Y (c : F) (n : ℕ) :
    ((C (C c) + X : BiPoly F) ^ 2) ^ n =
      ∑ l ∈ Finset.range (n + 1), C (C ((Nat.choose n l : F) * (c ^ 2) ^ (n - l))) * X ^ (2 * l) := by
  have hsq : (C (C c) + X : BiPoly F) ^ 2 = C (C (c ^ 2)) + X ^ 2 := by
    rw [add_sq_bi, ← map_pow, ← map_pow]
  rw [hsq, add_comm, add_pow]
  apply Finset.sum_congr rfl; intro l _
  rw [← pow_mul, ← map_pow, ← map_pow, mul_assoc,
    show C (C ((c ^ 2) ^ (n - l))) * (Nat.choose n l : BiPoly F) =
      C (C ((Nat.choose n l : F) * (c ^ 2) ^ (n - l))) by simp [mul_comm], mul_comm]

/-- Helper: build `BiPoly F` from an explicit bounded coefficient table `tbl : ℕ → ℕ → F`. -/
private noncomputable def mkEvenBi (B A : ℕ) (tbl : ℕ → ℕ → F) : BiPoly F :=
  ∑ b ∈ Finset.range (B + 1),
    C (∑ a ∈ Finset.range (A + 1), C (tbl a b) * X ^ (2 * a)) * X ^ b

private lemma coeff_mkEvenBi (B A : ℕ) (tbl : ℕ → ℕ → F) (j i : ℕ) :
    ((mkEvenBi B A tbl).coeff j).coeff i =
      if j ≤ B ∧ i % 2 = 0 ∧ i / 2 ≤ A then tbl (i / 2) j else 0 := by
  unfold mkEvenBi
  rw [finset_sum_coeff, finset_sum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hj : j ≤ B
  · rw [Finset.sum_eq_single j]
    · rw [if_pos rfl, finset_sum_coeff]
      simp_rw [coeff_C_mul_X_pow]
      by_cases hi : i % 2 = 0 ∧ i / 2 ≤ A
      · rw [Finset.sum_eq_single (i / 2)]
        · rw [if_pos (by omega), if_pos ⟨hj, hi⟩]
        · intro a _ hne; rw [if_neg (by omega)]
        · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
      · rw [if_neg (by tauto)]
        apply Finset.sum_eq_zero; intro a ha
        have := Finset.mem_range.mp ha
        rw [if_neg (by omega)]
    · intro b _ hne; rw [if_neg hne.symm, coeff_zero]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  · rw [if_neg (by tauto)]
    apply Finset.sum_eq_zero; intro b hb
    have := Finset.mem_range.mp hb
    rw [if_neg (by omega), coeff_zero]

private lemma coeff_expand_two_bi (P : BiPoly F) (j : ℕ) :
    (Polynomial.expand (Polynomial F) 2 P).coeff j =
      if j % 2 = 0 then P.coeff (j / 2) else 0 := by
  rw [Polynomial.coeff_expand (by norm_num : 0 < 2)]
  by_cases h : 2 ∣ j
  · have h0 : j % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [if_pos h, if_pos h0]
  · have h0 : ¬ j % 2 = 0 := fun hm => h (Nat.dvd_of_mod_eq_zero hm)
    rw [if_neg h, if_neg h0]

/-- Helper: squaring + `V * sq` preserves `(1, 2)`-weighted order!
If `weightedOrdGE 2 m1 Pe` and `weightedOrdGE 2 m2 Po` with `2 * m1 ≥ M` and `2 * m2 + 2 ≥ M`,
then `weightedOrdGE 2 M (Pe ^ 2 + X * Po ^ 2)`! -/
theorem weightedOrdGE_sq_add_X_mul_sq (Pe Po : BiPoly F) (m1 m2 M : ℕ)
    (hPe : weightedOrdGE 2 m1 Pe) (hPo : weightedOrdGE 2 m2 Po)
    (hm1 : M ≤ 2 * m1) (hm2 : M ≤ 2 * m2 + 2) :
    weightedOrdGE 2 M (Pe ^ 2 + X * Po ^ 2) := by
  intro j
  rw [coeff_add]
  have hsq_coeff : ∀ (P : BiPoly F) (n : ℕ), (P ^ 2).coeff n =
      if n % 2 = 0 then (P.coeff (n / 2)) ^ 2 else 0 := by
    intro P n
    induction P using Polynomial.induction_on' generalizing n with
    | add a b ha hb =>
        rw [add_sq_bi, coeff_add, ha, hb, coeff_add]
        split_ifs
        · rw [add_sq_poly]
        · simp
    | monomial k c =>
        simp only [monomial_pow, coeff_monomial]
        by_cases h1 : n % 2 = 0
        · by_cases h2 : k = n / 2
          · subst h2; simp [h1, show n / 2 * 2 = n by omega]
          · simp [h1, h2, show k * 2 ≠ n by omega]
        · simp [h1, show k * 2 ≠ n by omega]
  apply dvd_add
  · rw [hsq_coeff]
    split_ifs with hj
    · have h1 := hPe (j / 2)
      have h2 : X ^ (2 * (m1 - 2 * (j / 2))) ∣ (Pe.coeff (j / 2)) ^ 2 := by
        rw [pow_mul']; exact pow_dvd_pow_of_dvd h1 2
      exact (pow_dvd_pow X (by omega : M - 2 * j ≤ 2 * (m1 - 2 * (j / 2)))).trans h2
    · exact dvd_zero _
  · cases j with
    | zero => rw [coeff_X_mul_zero]; exact dvd_zero _
    | succ j' =>
        rw [coeff_X_mul, hsq_coeff]
        split_ifs with hj'
        · have h1 := hPo (j' / 2)
          have h2 : X ^ (2 * (m2 - 2 * (j' / 2))) ∣ (Po.coeff (j' / 2)) ^ 2 := by
            rw [pow_mul']; exact pow_dvd_pow_of_dvd h1 2
          exact (pow_dvd_pow X (by omega : M - 2 * (j' + 1) ≤ 2 * (m2 - 2 * (j' / 2)))).trans h2
        · exact dvd_zero _

/-- Helper: `weightedOrdGE 2 m (C (X ^ 2) * P)` from `weightedOrdGE 2 (m - 2) P`, etc., and
exact `shiftBi` expansion of ANY `kerDBasisPoly (k, r, b, a)`! -/
private lemma shiftBi_monom_even (x0 y0 c : F) (a1 b1 : ℕ) (i j : ℕ) :
    ((shiftBi x0 y0 (C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1)).coeff j).coeff i =
      if i % 2 = 0 ∧ j % 2 = 0 then
        c * (Nat.choose a1 (i / 2) : F) * (x0 ^ 2) ^ (a1 - i / 2) *
          ((Nat.choose b1 (j / 2) : F) * (y0 ^ 2) ^ (b1 - j / 2))
      else 0 := by
  rw [shiftBi_mul, shiftBi_mul, shiftBi_C, shiftBi_pow, shiftBi_C, shiftBi_pow, shiftBi_pow, shiftBi_X]
  simp only [C_comp, pow_comp, X_comp, ← map_pow, shift_even_X, shift_even_Y]
  rw [show C (C c) *
      C (∑ l ∈ Finset.range (a1 + 1), C ((Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l)) * X ^ (2 * l)) *
      (∑ m ∈ Finset.range (b1 + 1), C (C ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * m)) =
      ∑ m ∈ Finset.range (b1 + 1),
        C (∑ l ∈ Finset.range (a1 + 1),
          C (c * (Nat.choose a1 l : F) * (x0 ^ 2) ^ (a1 - l) *
            ((Nat.choose b1 m : F) * (y0 ^ 2) ^ (b1 - m))) * X ^ (2 * l)) * X ^ (2 * m) by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
    rw [← mul_assoc, ← map_mul, ← map_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1; congr 1; apply Finset.sum_congr rfl; intro l _
    simp only [map_mul]; ring]
  rw [finset_sum_coeff, finset_sum_coeff]; simp_rw [coeff_C_mul_X_pow]
  split_ifs with hij
  · rcases hij with ⟨hi, hj⟩
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

private lemma shiftBi_monom_Y_mul_even (x0 y0 c : F) (a1 b1 : ℕ) (i j : ℕ) :
    ((shiftBi x0 y0 (C (C c) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1)).coeff j).coeff i =
      if i % 2 = 0 ∧ j % 2 = 0 then
        c * y0 * (Nat.choose a1 (i / 2) : F) * (x0 ^ 2) ^ (a1 - i / 2) *
          ((Nat.choose b1 (j / 2) : F) * (y0 ^ 2) ^ (b1 - j / 2))
      else if i % 2 = 0 ∧ j % 2 = 1 then
        c * (Nat.choose a1 (i / 2) : F) * (x0 ^ 2) ^ (a1 - i / 2) *
          ((Nat.choose b1 (j / 2) : F) * (y0 ^ 2) ^ (b1 - j / 2))
      else 0 := by
  have hrew : C (C c) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 =
      X * (C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) := by ring
  rw [hrew, shiftBi_mul, shiftBi_X, add_mul, coeff_add, coeff_add,
    coeff_C_mul, coeff_C_mul]
  rw [shiftBi_monom_even x0 y0 c a1 b1 i j]
  cases j with
  | zero =>
      rw [coeff_X_mul_zero]
      simp only [Nat.zero_mod, zero_ne_one, and_false, ↓reduceIte, coeff_zero, add_zero, Nat.zero_div, Nat.sub_zero]
      split_ifs <;> ring
  | succ j' =>
      rw [coeff_X_mul, shiftBi_monom_even x0 y0 c a1 b1 i j']
      by_cases hi : i % 2 = 0
      · by_cases hj : (j' + 1) % 2 = 0
        · have hj' : j' % 2 = 1 := by omega
          simp only [hi, hj, hj', and_self, one_ne_zero, and_false, ↓reduceIte, add_zero]; ring
        · have hj1 : (j' + 1) % 2 = 1 := by omega
          have hj' : j' % 2 = 0 := by omega
          have hd : j' / 2 = (j' + 1) / 2 := by omega
          simp only [hi, hj, hj1, hj', one_ne_zero, true_and, and_self, and_false, ↓reduceIte, mul_zero, zero_add, hd]
      · simp only [hi, false_and, ↓reduceIte, mul_zero, add_zero]

private lemma shiftBi_monom_X_mul_even (x0 y0 c : F) (a1 b1 : ℕ) (i j : ℕ) :
    ((shiftBi x0 y0 (C (C c) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1)).coeff j).coeff i =
      if i % 2 = 0 ∧ j % 2 = 0 then
        c * x0 * (Nat.choose a1 (i / 2) : F) * (x0 ^ 2) ^ (a1 - i / 2) *
          ((Nat.choose b1 (j / 2) : F) * (y0 ^ 2) ^ (b1 - j / 2))
      else if i % 2 = 1 ∧ j % 2 = 0 then
        c * (Nat.choose a1 (i / 2) : F) * (x0 ^ 2) ^ (a1 - i / 2) *
          ((Nat.choose b1 (j / 2) : F) * (y0 ^ 2) ^ (b1 - j / 2))
      else 0 := by
  have hrew : C (C c) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1 =
      C X * (C (C c) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) := by ring
  rw [hrew, shiftBi_mul, shiftBi_C, X_comp, coeff_C_mul, add_mul, coeff_add, coeff_C_mul]
  rw [shiftBi_monom_even x0 y0 c a1 b1 i j]
  cases i with
  | zero =>
      rw [coeff_X_mul_zero]
      simp only [Nat.zero_mod, zero_ne_one, false_and, ↓reduceIte, add_zero, Nat.zero_div, Nat.sub_zero]
      split_ifs <;> ring
  | succ i' =>
      rw [coeff_X_mul, shiftBi_monom_even x0 y0 c a1 b1 i' j]
      by_cases hj : j % 2 = 0
      · by_cases hi : (i' + 1) % 2 = 0
        · have hi' : i' % 2 = 1 := by omega
          simp only [hi, hi', hj, and_self, one_ne_zero, false_and, ↓reduceIte, add_zero]; ring
        · have hi1 : (i' + 1) % 2 = 1 := by omega
          have hi' : i' % 2 = 0 := by omega
          have hd : i' / 2 = (i' + 1) / 2 := by omega
          simp only [hi, hi1, hi', hj, one_ne_zero, and_true, and_self, false_and, ↓reduceIte, mul_zero, zero_add, hd]
      · simp only [hj, and_false, ↓reduceIte, mul_zero, add_zero]

private lemma shiftBi_sum {ι : Type*} (S : Finset ι) (x0 y0 : F) (g : ι → BiPoly F) :
    shiftBi x0 y0 (∑ e ∈ S, g e) = ∑ e ∈ S, shiftBi x0 y0 (g e) := by
  classical
  induction S using Finset.induction_on with
  | empty => unfold shiftBi; simp
  | insert a S ha ih => rw [Finset.sum_insert ha, shiftBi_add, ih, Finset.sum_insert ha]

/-- **Helper: `kerD1_weighted_decomp` (`deg_R = 1` exact `(4k + 2)`-weighted decomposition):**
For `F = f_0 + f_1 R ∈ K_{W_F}(1)` with `twOrdGE (localShift F) k`:
`s * f_0(x0 + s, y0 + v) + v * f_1(x0 + s, y0 + v) = Pe(s, v^2) + v * Po(s, v^2)`
where `Pe = s A0(s^2, V)`, `Po = A1(s^2, V)`, `2 * Pe.natDegree ≤ f_0.natDegree`,
`2 * Po.natDegree + 1 ≤ f_1.natDegree + 1`, and `weightedOrdGE 2 (4 * k + 2) (Pe^2 + V * Po^2)`! -/
theorem kerD1_weighted_decomp {wY W_F k : ℕ} (hwY : 0 < wY) (x0 y0 : F)
    (f_coord : KerDIdx wY W_F 1 → F)
    (hvan : twOrdGE (∑ e : KerDIdx wY W_F 1, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) k) :
    let Fpoly : ContactPoly F := ∑ e : KerDIdx wY W_F 1, cC (f_coord e) * kerDBasisPoly e.1
    ∃ Pe Po : BiPoly F,
      shiftBi x0 y0 (Fpoly.coeff 0) * C X + shiftBi x0 y0 (Fpoly.coeff 1) * X =
        Polynomial.expand (Polynomial F) 2 Pe + X * Polynomial.expand (Polynomial F) 2 Po ∧
      2 * Pe.natDegree ≤ (Fpoly.coeff 0).natDegree ∧
      2 * Po.natDegree ≤ (Fpoly.coeff 1).natDegree ∧
      weightedOrdGE 2 (2 * k + 1) Pe ∧
      weightedOrdGE 2 (2 * k) Po ∧
      weightedOrdGE 2 (4 * k + 2) (Pe ^ 2 + X * Po ^ 2) := by
  intro Fpoly
  -- Reuse the exact same A0, A1, C0 tables as kerD1_local_ords!
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
  have hNF0 : ∀ idx : LocalBasisIdx k 1,
      (∑ e : KerDIdx wY W_F 1, f_coord e * kerDLocalNF k 1 x0 y0 e.1 idx) = 0 := by
    apply localBasis_linearIndependent_mod k 1
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
        rw [hms]; refine congrArg₂ (· - ·) rfl ?_
        refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
        simp only [map_mul, mul_assoc]
      rw [hrew]
      have hsum_tw : ∀ (S : Finset (KerDIdx wY W_F 1)) (g : KerDIdx wY W_F 1 → LocalPoly F),
          (∀ e ∈ S, twOrdGE (g e) k) → twOrdGE (∑ e ∈ S, g e) k := by
        intro S g hg; classical
        induction S using Finset.induction_on with
        | empty => simp [twOrdGE_of_zero]
        | insert a S ha ih =>
            rw [Finset.sum_insert ha]
            exact twOrdGE_add (hg a (Finset.mem_insert_self _ _)) (ih fun y hy => hg y (Finset.mem_insert_of_mem hy))
      apply hsum_tw; intro e _
      have hmem := (mem_kerDIdxFinset_iff wY W_F 1 hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      simpa using twOrdGE_mul (twOrdGE_zero _)
        (twOrdGE_kerDLocalPoly_sub_NF k 1 x0 y0 e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 hmem.1 hmem.2.1)
    have hcomb := twOrdGE_sub hvan hdiff
    rwa [sub_sub_cancel (G := LocalPoly F)] at hcomb
  have hred_any : ∀ (q j a' b' : ℕ) (idx : LocalBasisIdx k 1), j < 2 →
      reduceMonomialCoords k 1 q j a' b' idx = if idx.1 = (q, j, a', b') then 1 else 0 := by
    intro q j a' b' idx hj
    cases a' with
    | zero => rfl
    | succ a'' =>
        unfold reduceMonomialCoords
        by_cases hlt : q + (a'' + 1) + b' < k
        · simp [show ¬ (q + (a'' + 1) + b' ≥ k) by omega, hj]
        · rw [if_pos (by omega)]
          have hne : idx.1 ≠ (q, j, a'' + 1, b') := by
            rcases idx with ⟨⟨q', j', a0, b0⟩, hidx⟩
            intro heq
            have h2 := ((mem_localBasisFinset_iff k 1 q' j' a0 b0).mp hidx).2.1
            simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨rfl, rfl, rfl, rfl⟩
            omega
          simp [hne]
  have hA0_zero : ∀ a' b', a' + b' < k → A0 a' b' = 0 := by
    intro a' b' hlt
    have hmem : (0, 0, a', b') ∈ localBasisFinset k 1 :=
      (mem_localBasisFinset_iff k 1 0 0 a' b').mpr ⟨by omega, by omega, Or.inl (by omega)⟩
    let idx : LocalBasisIdx k 1 := ⟨(0, 0, a', b'), hmem⟩
    rw [← hNF0 idx]; dsimp [A0]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hm := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
    unfold kerDLocalNF; dsimp only
    rcases (show (k1 = 0 ∧ r1 = 0) ∨ (k1 = 1 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) by omega) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [true_and, ↓reduceIte, hred_any 0 0 _ _ idx (by omega), idx, Prod.mk.injEq]
      by_cases ha : a' ≤ a1 <;> by_cases hb : b' ≤ b1
      · rw [Finset.sum_eq_single a', Finset.sum_eq_single b']
        · simp; ring
        · intro b'' _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
        · intro a'' _ hne; apply Finset.sum_eq_zero; intro b'' _; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := b') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a'' _; apply Finset.sum_eq_zero; intro b'' hb''
        have := Finset.mem_range.mp hb''; simp [show b' ≠ b'' by omega]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have := Finset.mem_range.mp ha''; simp [show a' ≠ a'' by omega]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have := Finset.mem_range.mp ha''; simp [show a' ≠ a'' by omega]
    · simp [hred_any 0 1 _ _ idx (by omega), idx]
    · simp only [true_and, zero_ne_one, one_ne_zero, and_false, false_and, ↓reduceIte,
        hred_any 0 0 _ _ idx (by omega), hred_any 0 1 _ _ idx (by omega), hred_any 1 0 _ _ idx (by omega),
        idx, Prod.mk.injEq, Nat.cast_zero, mul_zero, add_zero]
      by_cases ha : a' ≤ a1 <;> by_cases hb : b' ≤ b1
      · rw [Finset.sum_eq_single a', Finset.sum_eq_single b']
        · simp; ring
        · intro b'' _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
        · intro a'' _ hne; apply Finset.sum_eq_zero; intro b'' _; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := b') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a'' _; apply Finset.sum_eq_zero; intro b'' hb''
        have := Finset.mem_range.mp hb''; simp [show b' ≠ b'' by omega]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have := Finset.mem_range.mp ha''; simp [show a' ≠ a'' by omega]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have := Finset.mem_range.mp ha''; simp [show a' ≠ a'' by omega]
  have hA1_zero : ∀ a' b', a' + b' < k → A1 a' b' = 0 := by
    intro a' b' hlt
    have hmem : (0, 1, a', b') ∈ localBasisFinset k 1 :=
      (mem_localBasisFinset_iff k 1 0 1 a' b').mpr ⟨by omega, by omega, Or.inl (by omega)⟩
    let idx : LocalBasisIdx k 1 := ⟨(0, 1, a', b'), hmem⟩
    rw [← hNF0 idx]; dsimp [A1]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hm := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
    unfold kerDLocalNF; dsimp only
    rcases (show (k1 = 0 ∧ r1 = 0) ∨ (k1 = 1 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) by omega) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [hred_any 0 0 _ _ idx (by omega), idx]
    · simp only [true_and, ↓reduceIte, hred_any 0 1 _ _ idx (by omega), idx, Prod.mk.injEq]
      by_cases ha : a' ≤ a1 <;> by_cases hb : b' ≤ b1
      · rw [Finset.sum_eq_single a', Finset.sum_eq_single b']
        · simp; ring
        · intro b'' _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
        · intro a'' _ hne; apply Finset.sum_eq_zero; intro b'' _; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := b') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a'' _; apply Finset.sum_eq_zero; intro b'' hb''
        have := Finset.mem_range.mp hb''; simp [show b' ≠ b'' by omega]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have := Finset.mem_range.mp ha''; simp [show a' ≠ a'' by omega]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have := Finset.mem_range.mp ha''; simp [show a' ≠ a'' by omega]
    · simp only [true_and, zero_ne_one, one_ne_zero, false_and, and_false, ↓reduceIte,
        hred_any 0 0 _ _ idx (by omega), hred_any 0 1 _ _ idx (by omega), hred_any 1 0 _ _ idx (by omega),
        idx, Prod.mk.injEq, Nat.cast_zero, mul_zero, zero_add, add_zero]
      by_cases ha : a' ≤ a1 <;> by_cases hb : b' ≤ b1
      · rw [Finset.sum_eq_single a', Finset.sum_eq_single b']
        · simp; ring
        · intro b'' _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
        · intro a'' _ hne; apply Finset.sum_eq_zero; intro b'' _; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := b') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a'' _; apply Finset.sum_eq_zero; intro b'' hb''
        have := Finset.mem_range.mp hb''; simp [show b' ≠ b'' by omega]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have := Finset.mem_range.mp ha''; simp [show a' ≠ a'' by omega]
      · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a') (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
        symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a'' ha''; apply Finset.sum_eq_zero; intro b'' _
        have := Finset.mem_range.mp ha''; simp [show a' ≠ a'' by omega]
  -- Read off shiftBi(f0) and shiftBi(f1) coefficients cleanly via shiftBi_monom_*!
  have hshift_f0 : ∀ i j, ((shiftBi x0 y0 (Fpoly.coeff 0)).coeff j).coeff i =
      if i % 2 = 0 ∧ j % 2 = 0 then A0 (i / 2) (j / 2)
      else if i % 2 = 0 ∧ j % 2 = 1 then C0 (i / 2) (j / 2)
      else 0 := by
    intro i j
    have hf0 : Fpoly.coeff 0 = ∑ e : KerDIdx wY W_F 1,
        if e.1.1 = 0 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 0 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else 0 := by
      dsimp [Fpoly]; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
      have hm := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
      rcases (show (k1 = 0 ∧ r1 = 0) ∨ (k1 = 1 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) by omega) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [true_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_zero, one_mul, one_mul,
          show C (C (C (f_coord ⟨(0, 0, b1, a1), he⟩))) * ((C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0, 0, b1, a1), he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by
          simp only [map_mul, map_pow]; ring, coeff_C, if_pos rfl]
      · simp only [one_ne_zero, false_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_one, pow_zero, mul_one,
          show ∀ (p q r : ContactPoly F), p * (X * q * r) = X * (p * q * r) by intros; ring, coeff_X_mul_zero]
      · simp only [one_ne_zero, and_false, ↓reduceIte, true_and]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_one, one_mul,
          show C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩))) * ((C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
            X * C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by
          simp only [map_mul, map_pow]; ring, coeff_add, coeff_C, if_pos rfl, coeff_X_mul_zero, add_zero]
    rw [hf0, shiftBi_sum, finset_sum_coeff, finset_sum_coeff]
    have hR : (if i % 2 = 0 ∧ j % 2 = 0 then A0 (i / 2) (j / 2)
        else if i % 2 = 0 ∧ j % 2 = 1 then C0 (i / 2) (j / 2) else 0) =
        ∑ e : KerDIdx wY W_F 1,
          if e.1.1 = 0 ∧ e.1.2.1 = 0 then
            (if i % 2 = 0 ∧ j % 2 = 0 then f_coord e * (Nat.choose e.1.2.2.2 (i / 2) : F) * (x0 ^ 2) ^ (e.1.2.2.2 - i / 2) *
              ((Nat.choose e.1.2.2.1 (j / 2) : F) * (y0 ^ 2) ^ (e.1.2.2.1 - j / 2)) else 0)
          else if e.1.1 = 0 ∧ e.1.2.1 = 1 then
            (if i % 2 = 0 ∧ j % 2 = 0 then f_coord e * y0 * (Nat.choose e.1.2.2.2 (i / 2) : F) * (x0 ^ 2) ^ (e.1.2.2.2 - i / 2) *
              ((Nat.choose e.1.2.2.1 (j / 2) : F) * (y0 ^ 2) ^ (e.1.2.2.1 - j / 2))
             else if i % 2 = 0 ∧ j % 2 = 1 then f_coord e * (Nat.choose e.1.2.2.2 (i / 2) : F) * (x0 ^ 2) ^ (e.1.2.2.2 - i / 2) *
              ((Nat.choose e.1.2.2.1 (j / 2) : F) * (y0 ^ 2) ^ (e.1.2.2.1 - j / 2)) else 0)
          else 0 := by
      dsimp [A0, C0]; split_ifs <;> first
        | (apply Finset.sum_congr rfl; intro e _; split_ifs <;> first | rfl | omega)
        | (symm; apply Finset.sum_eq_zero; intro e _; split_ifs <;> first | rfl | omega)
    rw [hR]; apply Finset.sum_congr rfl; intro e _
    by_cases he1 : e.1.1 = 0 ∧ e.1.2.1 = 0
    · simp only [he1, ↓reduceIte]
      exact shiftBi_monom_even x0 y0 (f_coord e) e.1.2.2.2 e.1.2.2.1 i j
    · by_cases he2 : e.1.1 = 0 ∧ e.1.2.1 = 1
      · simp only [he1, he2, ↓reduceIte]
        exact shiftBi_monom_Y_mul_even x0 y0 (f_coord e) e.1.2.2.2 e.1.2.2.1 i j
      · simp only [he1, he2, ↓reduceIte]; unfold shiftBi; simp
  have hshift_f1 : ∀ i j, ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff j).coeff i =
      if i % 2 = 0 ∧ j % 2 = 0 then A1 (i / 2) (j / 2)
      else if i % 2 = 1 ∧ j % 2 = 0 then C0 (i / 2) (j / 2)
      else 0 := by
    intro i j
    have hf1 : Fpoly.coeff 1 = ∑ e : KerDIdx wY W_F 1,
        if e.1.1 = 1 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 0 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * C X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else 0 := by
      dsimp [Fpoly]; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
      have hm := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
      rcases (show (k1 = 0 ∧ r1 = 0) ∨ (k1 = 1 ∧ r1 = 0) ∨ (k1 = 0 ∧ r1 = 1) by omega) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [zero_ne_one, one_ne_zero, false_and, and_false, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_zero, one_mul, one_mul,
          show C (C (C (f_coord ⟨(0, 0, b1, a1), he⟩))) * ((C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0, 0, b1, a1), he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by
          simp only [map_mul, map_pow]; ring, coeff_C, if_neg one_ne_zero]
      · simp only [true_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_one, pow_zero, mul_one,
          show C (C (C (f_coord ⟨(1, 0, b1, a1), he⟩))) * (X * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            X * C (C (C (f_coord ⟨(1, 0, b1, a1), he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by
          simp only [map_mul, map_pow]; ring, coeff_X_mul, coeff_C, if_pos rfl]
      · simp only [zero_ne_one, false_and, ↓reduceIte, true_and]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_one, one_mul,
          show C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩))) * ((C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
            X * C (C (C (f_coord ⟨(0, 1, b1, a1), he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by
          simp only [map_mul, map_pow]; ring, coeff_add, coeff_C, if_neg one_ne_zero, zero_add, coeff_X_mul, coeff_C, if_pos rfl]
    rw [hf1, shiftBi_sum, finset_sum_coeff, finset_sum_coeff]
    have hR : (if i % 2 = 0 ∧ j % 2 = 0 then A1 (i / 2) (j / 2)
        else if i % 2 = 1 ∧ j % 2 = 0 then C0 (i / 2) (j / 2) else 0) =
        ∑ e : KerDIdx wY W_F 1,
          if e.1.1 = 1 ∧ e.1.2.1 = 0 then
            (if i % 2 = 0 ∧ j % 2 = 0 then f_coord e * (Nat.choose e.1.2.2.2 (i / 2) : F) * (x0 ^ 2) ^ (e.1.2.2.2 - i / 2) *
              ((Nat.choose e.1.2.2.1 (j / 2) : F) * (y0 ^ 2) ^ (e.1.2.2.1 - j / 2)) else 0)
          else if e.1.1 = 0 ∧ e.1.2.1 = 1 then
            (if i % 2 = 0 ∧ j % 2 = 0 then f_coord e * x0 * (Nat.choose e.1.2.2.2 (i / 2) : F) * (x0 ^ 2) ^ (e.1.2.2.2 - i / 2) *
              ((Nat.choose e.1.2.2.1 (j / 2) : F) * (y0 ^ 2) ^ (e.1.2.2.1 - j / 2))
             else if i % 2 = 1 ∧ j % 2 = 0 then f_coord e * (Nat.choose e.1.2.2.2 (i / 2) : F) * (x0 ^ 2) ^ (e.1.2.2.2 - i / 2) *
              ((Nat.choose e.1.2.2.1 (j / 2) : F) * (y0 ^ 2) ^ (e.1.2.2.1 - j / 2)) else 0)
          else 0 := by
      dsimp [A1, C0]; split_ifs <;> first
        | (apply Finset.sum_congr rfl; intro e _; split_ifs <;> first | rfl | omega)
        | (symm; apply Finset.sum_eq_zero; intro e _; split_ifs <;> first | rfl | omega)
    rw [hR]; apply Finset.sum_congr rfl; intro e _
    by_cases he1 : e.1.1 = 1 ∧ e.1.2.1 = 0
    · simp only [he1, ↓reduceIte]
      exact shiftBi_monom_even x0 y0 (f_coord e) e.1.2.2.2 e.1.2.2.1 i j
    · by_cases he2 : e.1.1 = 0 ∧ e.1.2.1 = 1
      · simp only [he1, he2, ↓reduceIte]
        exact shiftBi_monom_X_mul_even x0 y0 (f_coord e) e.1.2.2.2 e.1.2.2.1 i j
      · simp only [he1, he2, ↓reduceIte]; unfold shiftBi; simp
  -- Bound supports of A0, A1 cleanly from natDegree of Fpoly.coeff 0 and Fpoly.coeff 1!
  have hshift_deg : ∀ g : BiPoly F, (shiftBi x0 y0 g).natDegree ≤ g.natDegree := by
    intro g; unfold shiftBi
    refine natDegree_comp_le.trans ?_
    have h1 : (g.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ g.natDegree := natDegree_map_le
    have h2 : (C (C y0) + X : BiPoly F).natDegree ≤ 1 := (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
    nlinarith only [h1, h2]
  have hA0_b : ∀ a' b', (Fpoly.coeff 0).natDegree / 2 < b' → A0 a' b' = 0 := by
    intro a' b' hb
    have h0 := hshift_f0 (2 * a') (2 * b')
    have hle := hshift_deg (Fpoly.coeff 0)
    have hz : (shiftBi x0 y0 (Fpoly.coeff 0)).coeff (2 * b') = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, coeff_zero] at h0; simpa using h0.symm
  have hA1_b : ∀ a' b', (Fpoly.coeff 1).natDegree / 2 < b' → A1 a' b' = 0 := by
    intro a' b' hb
    have h0 := hshift_f1 (2 * a') (2 * b')
    have hle := hshift_deg (Fpoly.coeff 1)
    have hz : (shiftBi x0 y0 (Fpoly.coeff 1)).coeff (2 * b') = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, coeff_zero] at h0; simpa using h0.symm
  have hA0_a : ∀ a' b', W_F / 2 < a' → A0 a' b' = 0 := by
    intro a' b' ha; dsimp [A0]; apply Finset.sum_eq_zero; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hm := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
    have ha1 : a1 < a' := by omega
    split_ifs <;> simp [Nat.choose_eq_zero_of_lt ha1]
  have hA1_a : ∀ a' b', W_F / 2 < a' → A1 a' b' = 0 := by
    intro a' b' ha; dsimp [A1]; apply Finset.sum_eq_zero; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hm := (mem_kerDIdxFinset_iff wY W_F 1 hwY k1 r1 b1 a1).mp he
    have ha1 : a1 < a' := by omega
    split_ifs <;> simp [Nat.choose_eq_zero_of_lt ha1]
  let Pe : BiPoly F := C X * mkEvenBi ((Fpoly.coeff 0).natDegree / 2) (W_F / 2) A0
  let Po : BiPoly F := mkEvenBi ((Fpoly.coeff 1).natDegree / 2) (W_F / 2) A1
  have hPe_eq : shiftBi x0 y0 (Fpoly.coeff 0) * C X + shiftBi x0 y0 (Fpoly.coeff 1) * X =
      Polynomial.expand (Polynomial F) 2 Pe + X * Polynomial.expand (Polynomial F) 2 Po := by
    ext j i
    have hRHS_X : (X * Polynomial.expand (Polynomial F) 2 Po).coeff j =
        if j = 0 then 0 else (Polynomial.expand (Polynomial F) 2 Po).coeff (j - 1) := by
      cases j with | zero => rw [coeff_X_mul_zero]; rfl | succ j' => rw [coeff_X_mul]; simp
    have hLHS_X : (shiftBi x0 y0 (Fpoly.coeff 1) * X).coeff j =
        if j = 0 then 0 else (shiftBi x0 y0 (Fpoly.coeff 1)).coeff (j - 1) := by
      cases j with | zero => rw [coeff_mul_X_zero]; rfl | succ j' => rw [coeff_mul_X]; simp
    rw [coeff_add, coeff_mul_C, hLHS_X, coeff_add, coeff_add, hRHS_X,
      coeff_expand_two_bi]
    have hLHS : ((shiftBi x0 y0 (Fpoly.coeff 0)).coeff j * X).coeff i +
        (if j = 0 then (0 : Polynomial F) else (shiftBi x0 y0 (Fpoly.coeff 1)).coeff (j - 1)).coeff i =
        (if i = 0 then 0 else ((shiftBi x0 y0 (Fpoly.coeff 0)).coeff j).coeff (i - 1)) +
        (if j = 0 then 0 else ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff (j - 1)).coeff i) := by
      congr 1
      · cases i with | zero => rw [coeff_mul_X_zero]; rfl | succ i' => rw [coeff_mul_X]; simp
      · split_ifs <;> simp
    rw [hLHS]
    cases j with
    | zero =>
        simp only [↓reduceIte, add_zero, Nat.zero_mod, Nat.zero_div, coeff_zero]
        dsimp [Pe]; rw [coeff_C_mul]
        cases i with
        | zero => rw [coeff_X_mul_zero]; rfl
        | succ i' =>
            rw [coeff_X_mul]
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
            rw [hshift_f0 i' 0, coeff_mkEvenBi]
            simp only [Nat.zero_mod, and_true, zero_ne_one, and_false, ↓reduceIte, Nat.zero_div]
            by_cases hi : i' % 2 = 0
            · rw [if_pos hi]; by_cases hle : i' / 2 ≤ W_F / 2
              · rw [if_pos ⟨Nat.zero_le _, hi, hle⟩]
              · rw [if_neg (by tauto), hA0_a (i' / 2) 0 (by omega)]
            · rw [if_neg hi, if_neg (by tauto)]
    | succ j' =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [hshift_f1 i j']
        by_cases hj : (j' + 1) % 2 = 0
        · rw [if_pos hj, coeff_expand_two_bi, if_neg (by omega : ¬ j' % 2 = 0), add_zero]
          dsimp [Pe]; rw [coeff_C_mul]
          cases i with
          | zero =>
              rw [coeff_X_mul_zero]
              simp only [↓reduceIte, zero_add]
              rw [if_neg (by omega), if_neg (by omega)]
          | succ i' =>
              rw [coeff_X_mul]
              simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
              rw [hshift_f0 i' (j' + 1), coeff_mkEvenBi]
              have hj' : j' % 2 = 1 := by omega
              have hf1z : (if (i' + 1) % 2 = 0 ∧ j' % 2 = 0 then A1 ((i' + 1) / 2) (j' / 2)
                  else if (i' + 1) % 2 = 1 ∧ j' % 2 = 0 then C0 ((i' + 1) / 2) (j' / 2) else 0) = 0 := by
                split_ifs <;> first | rfl | omega
              rw [hf1z, add_zero]
              by_cases hi : i' % 2 = 0
              · rw [if_pos ⟨hi, hj⟩]
                by_cases h1 : (j' + 1) / 2 ≤ (Fpoly.coeff 0).natDegree / 2
                · by_cases h2 : i' / 2 ≤ W_F / 2
                  · rw [if_pos ⟨h1, hi, h2⟩]
                  · rw [if_neg (by tauto), hA0_a (i' / 2) ((j' + 1) / 2) (by omega)]
                · rw [if_neg (by tauto), hA0_b (i' / 2) ((j' + 1) / 2) (by omega)]
              · rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto)]
        · have hj' : j' % 2 = 0 := by omega
          rw [if_neg hj, coeff_expand_two_bi, if_pos hj', zero_add]
          dsimp [Po]; rw [coeff_mkEvenBi]
          cases i with
          | zero =>
              simp only [hj', ↓reduceIte, zero_add, Nat.zero_mod, zero_ne_one, false_and, eq_self, true_and, Nat.zero_div, zero_le, and_true]
              by_cases h1 : j' / 2 ≤ (Fpoly.coeff 1).natDegree / 2
              · rw [if_pos h1]
              · rw [if_neg h1, hA1_b 0 (j' / 2) (by omega)]
          | succ i' =>
              simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
              rw [hshift_f0 i' (j' + 1)]
              by_cases hi : (i' + 1) % 2 = 0
              · have hi' : i' % 2 = 1 := by omega
                rw [if_neg (by omega), if_neg (by omega), zero_add, if_pos ⟨hi, hj'⟩]
                by_cases h1 : j' / 2 ≤ (Fpoly.coeff 1).natDegree / 2
                · by_cases h2 : (i' + 1) / 2 ≤ W_F / 2
                  · rw [if_pos ⟨h1, hi, h2⟩]
                  · rw [if_neg (by tauto), hA1_a ((i' + 1) / 2) (j' / 2) (by omega)]
                · rw [if_neg (by tauto), hA1_b ((i' + 1) / 2) (j' / 2) (by omega)]
              · have hi' : i' % 2 = 0 := by omega
                have hdiv : i' / 2 = (i' + 1) / 2 := by omega
                have hjdiv : (j' + 1) / 2 = j' / 2 := by omega
                rw [if_neg (by omega), if_pos ⟨hi', show (j' + 1) % 2 = 1 by omega⟩,
                  if_neg (by omega), if_pos ⟨show (i' + 1) % 2 = 1 by omega, hj'⟩,
                  if_neg (by tauto), hdiv, hjdiv]
                exact CharTwo.add_self_eq_zero _
  have hPe_deg : 2 * Pe.natDegree ≤ (Fpoly.coeff 0).natDegree := by
    have hle : Pe.natDegree ≤ (Fpoly.coeff 0).natDegree / 2 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
      ext i; dsimp [Pe]; rw [coeff_C_mul]
      cases i with
      | zero => rw [coeff_X_mul_zero]
      | succ i' => rw [coeff_X_mul, coeff_mkEvenBi, if_neg (by omega)]
    omega
  have hPo_deg : 2 * Po.natDegree ≤ (Fpoly.coeff 1).natDegree := by
    have hle : Po.natDegree ≤ (Fpoly.coeff 1).natDegree / 2 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
      ext i; dsimp [Po]; rw [coeff_mkEvenBi]; simp [show ¬ j ≤ (Fpoly.coeff 1).natDegree / 2 by omega]
    omega
  have hPe_ord : weightedOrdGE 2 (2 * k + 1) Pe := by
    intro j; rw [X_pow_dvd_iff]; intro i hi
    dsimp [Pe]; rw [coeff_C_mul]
    cases i with
    | zero => rw [coeff_X_mul_zero]
    | succ i' =>
        rw [coeff_X_mul]
        simp only [coeff_mkEvenBi]
        split_ifs with h
        · exact hA0_zero (i' / 2) j (by omega)
        · rfl
  have hPo_ord : weightedOrdGE 2 (2 * k) Po := by
    intro j; rw [X_pow_dvd_iff]; intro i hi
    dsimp [Po]; rw [coeff_mkEvenBi]
    split_ifs with h
    · exact hA1_zero (i / 2) j (by omega)
    · rfl
  exact ⟨Pe, Po, hPe_eq, hPe_deg, hPo_deg, hPe_ord, hPo_ord,
    weightedOrdGE_sq_add_X_mul_sq Pe Po (2 * k + 1) (2 * k) (4 * k + 2) hPe_ord hPo_ord (by omega) (by omega)⟩

/-- **Main `deg_R = 2` Local Order & `(4k + 4)`-Weighted Decomposition Theorem (`kerD2_local_ords`):**
If `F = f_0 + f_1 R + f_2 R^2 ∈ K_{W_F}(2)` has `twOrdGE (localShift x0 y0 F) k`, then:
1. `biMultGE x0 y0 f_0 (2 * k - 2)`, `biMultGE x0 y0 f_1 (2 * k - 1)`, `biMultGE x0 y0 f_2 (2 * k - 2)`;
2. `s^2 f_0(x0 + s, y0 + v) + s v f_1(x0 + s, y0 + v) + v^2 f_2(x0 + s, y0 + v) = Pe(s, v^2) + v * Po(s, v^2)`
   where `2 * Pe.natDegree ≤ max (deg_Y f_0) (deg_Y f_2 + 2)`, `2 * Po.natDegree ≤ deg_Y f_1`,
   `weightedOrdGE 2 (2 * k + 2) Pe`, `weightedOrdGE 2 (2 * k + 1) Po`, AND
   `weightedOrdGE 2 (4 * k + 4) (Pe^2 + V * Po^2)`! -/
theorem kerD2_local_ords {wY W_F k : ℕ} (hwY : 0 < wY) (x0 y0 : F)
    (f_coord : KerDIdx wY W_F 2 → F)
    (hvan : twOrdGE (∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) k) :
    let Fpoly : ContactPoly F := ∑ e : KerDIdx wY W_F 2, cC (f_coord e) * kerDBasisPoly e.1
    biMultGE x0 y0 (Fpoly.coeff 0) (2 * k - 2) ∧
    biMultGE x0 y0 (Fpoly.coeff 1) (2 * k - 1) ∧
    biMultGE x0 y0 (Fpoly.coeff 2) (2 * k - 2) ∧
    ∃ Pe Po : BiPoly F,
      shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) +
        shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X) +
        shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2 =
        Polynomial.expand (Polynomial F) 2 Pe + X * Polynomial.expand (Polynomial F) 2 Po ∧
      2 * Pe.natDegree ≤ max (Fpoly.coeff 0).natDegree ((Fpoly.coeff 2).natDegree + 2) ∧
      2 * Po.natDegree ≤ (Fpoly.coeff 1).natDegree ∧
      weightedOrdGE 2 (2 * k + 2) Pe ∧
      weightedOrdGE 2 (2 * k + 1) Po ∧
      weightedOrdGE 2 (4 * k + 4) (Pe ^ 2 + X * Po ^ 2) := by
  intro Fpoly
  -- 5 shifted tables A0, A1, A2, C0, C1 for the 5 (k1, r1) pairs with k1 + r1 ≤ 2!
  let binomWt (e : KerDIdx wY W_F 2) (a' b' : ℕ) : F :=
    f_coord e * (Nat.choose e.1.2.2.2 a' : F) * (x0 ^ 2) ^ (e.1.2.2.2 - a') *
      ((Nat.choose e.1.2.2.1 b' : F) * (y0 ^ 2) ^ (e.1.2.2.1 - b'))
  let A0 (a' b' : ℕ) : F := ∑ e : KerDIdx wY W_F 2,
    if e.1.1 = 0 ∧ e.1.2.1 = 0 then binomWt e a' b'
    else if e.1.1 = 0 ∧ e.1.2.1 = 1 then y0 * binomWt e a' b' else 0
  let A1 (a' b' : ℕ) : F := ∑ e : KerDIdx wY W_F 2,
    if e.1.1 = 1 ∧ e.1.2.1 = 0 then binomWt e a' b'
    else if e.1.1 = 0 ∧ e.1.2.1 = 1 then x0 * binomWt e a' b'
    else if e.1.1 = 1 ∧ e.1.2.1 = 1 then y0 * binomWt e a' b' else 0
  let A2 (a' b' : ℕ) : F := ∑ e : KerDIdx wY W_F 2,
    if e.1.1 = 2 ∧ e.1.2.1 = 0 then binomWt e a' b'
    else if e.1.1 = 1 ∧ e.1.2.1 = 1 then x0 * binomWt e a' b' else 0
  let C0 (a' b' : ℕ) : F := ∑ e : KerDIdx wY W_F 2,
    if e.1.1 = 0 ∧ e.1.2.1 = 1 then binomWt e a' b' else 0
  let C1 (a' b' : ℕ) : F := ∑ e : KerDIdx wY W_F 2,
    if e.1.1 = 1 ∧ e.1.2.1 = 1 then binomWt e a' b' else 0
  -- Step 1: NF vanishes on every idx : LocalBasisIdx k 2!
  have hNF0 : ∀ idx : LocalBasisIdx k 2,
      (∑ e : KerDIdx wY W_F 2, f_coord e * kerDLocalNF k 2 x0 y0 e.1 idx) = 0 := by
    apply localBasis_linearIndependent_mod k 2
    have hdiff : twOrdGE ((∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) -
        ∑ idx : LocalBasisIdx k 2, locC (∑ e : KerDIdx wY W_F 2, f_coord e * kerDLocalNF k 2 x0 y0 e.1 idx) *
          localBasisElem idx.1) k := by
      have hrew : (∑ e : KerDIdx wY W_F 2, locC (f_coord e) * kerDLocalPoly x0 y0 e.1) -
          ∑ idx : LocalBasisIdx k 2, locC (∑ e : KerDIdx wY W_F 2, f_coord e * kerDLocalNF k 2 x0 y0 e.1 idx) *
            localBasisElem idx.1 =
          ∑ e : KerDIdx wY W_F 2, locC (f_coord e) *
            (kerDLocalPoly x0 y0 e.1 -
              ∑ idx : LocalBasisIdx k 2, locC (kerDLocalNF k 2 x0 y0 e.1 idx) * localBasisElem idx.1) := by
        simp_rw [locC, map_sum, Finset.sum_mul]
        rw [Finset.sum_comm, ← Finset.sum_sub_distrib (G := LocalPoly F)]
        apply Finset.sum_congr rfl; intro e _
        have hms : ∀ x y z : LocalPoly F, x * (y - z) = x * y - x * z := fun x y z =>
          eq_sub_of_add_eq (G := LocalPoly F) (by rw [← mul_add, sub_add_cancel (G := LocalPoly F)])
        rw [hms]; refine congrArg₂ (· - ·) rfl ?_
        refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
        simp only [map_mul, mul_assoc]
      rw [hrew]
      have hsum_tw : ∀ (S : Finset (KerDIdx wY W_F 2)) (g : KerDIdx wY W_F 2 → LocalPoly F),
          (∀ e ∈ S, twOrdGE (g e) k) → twOrdGE (∑ e ∈ S, g e) k := by
        intro S g hg; classical
        induction S using Finset.induction_on with
        | empty => simp [twOrdGE_of_zero]
        | insert a S ha ih =>
            rw [Finset.sum_insert ha]
            exact twOrdGE_add (hg a (Finset.mem_insert_self _ _)) (ih fun y hy => hg y (Finset.mem_insert_of_mem hy))
      apply hsum_tw; intro e _
      have hmem := (mem_kerDIdxFinset_iff wY W_F 2 hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      simpa using twOrdGE_mul (twOrdGE_zero _)
        (twOrdGE_kerDLocalPoly_sub_NF k 2 x0 y0 e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 hmem.1 hmem.2.1)
    have hcomb := twOrdGE_sub hvan hdiff
    rwa [sub_sub_cancel (G := LocalPoly F)] at hcomb
  -- Exact closed form of reduceMonomialCoords k 2 for ALL j ≤ 2!
  have hred_lt2 : ∀ (q j a' b' : ℕ) (idx : LocalBasisIdx k 2), j < 2 →
      reduceMonomialCoords k 2 q j a' b' idx = if idx.1 = (q, j, a', b') then 1 else 0 := by
    intro q j a' b' idx hj
    cases a' with
    | zero => rfl
    | succ a'' =>
        unfold reduceMonomialCoords
        by_cases hlt : q + (a'' + 1) + b' < k
        · simp [show ¬ (q + (a'' + 1) + b' ≥ k) by omega, hj]
        · rw [if_pos (by omega)]
          have hne : idx.1 ≠ (q, j, a'' + 1, b') := by
            rcases idx with ⟨⟨q', j', a0, b0⟩, hidx⟩
            intro heq
            have h2 := ((mem_localBasisFinset_iff k 2 q' j' a0 b0).mp hidx).2.1
            simp only [Prod.mk.injEq] at heq
            rcases heq with ⟨rfl, rfl, rfl, rfl⟩
            omega
          simp [hne]
  have hred_j2 : ∀ (a' b' : ℕ) (idx : LocalBasisIdx k 2),
      reduceMonomialCoords k 2 0 2 a' b' idx =
        match a' with
        | 0 => if idx.1 = (0, 2, 0, b') then 1 else 0
        | a'' + 1 =>
            if a'' + 1 + b' < k then
              (if idx.1 = (0, 0, a'', b' + 1) then 1 else 0) +
              (if idx.1 = (2, 0, a'', b') then 1 else 0)
            else 0 := by
    intro a' b' idx
    cases a' with
    | zero => rfl
    | succ a'' =>
        unfold reduceMonomialCoords
        dsimp only
        by_cases hlt : a'' + 1 + b' < k
        · rw [if_neg (by omega), if_neg (by omega), hred_lt2 0 0 a'' (b' + 1) idx (by omega),
            hred_lt2 2 0 a'' b' idx (by omega), if_pos hlt]
        · rw [if_pos (by omega), if_neg hlt]
  -- Helper to extract one exact binomial sum at (a0, b0):
  have hsum_single_ab : ∀ (a1 b1 a0 b0 : ℕ) (c : F),
      (∑ a' ∈ Finset.range (a1 + 1), ∑ b' ∈ Finset.range (b1 + 1),
        (Nat.choose a1 a' : F) * (x0 ^ 2) ^ (a1 - a') *
          ((Nat.choose b1 b' : F) * (y0 ^ 2) ^ (b1 - b')) *
          (if a0 = a' ∧ b0 = b' then c else 0)) =
      c * ((Nat.choose a1 a0 : F) * (x0 ^ 2) ^ (a1 - a0) *
        ((Nat.choose b1 b0 : F) * (y0 ^ 2) ^ (b1 - b0))) := by
    intro a1 b1 a0 b0 c
    by_cases ha : a0 ≤ a1 <;> by_cases hb : b0 ≤ b1
    · rw [Finset.sum_eq_single a0, Finset.sum_eq_single b0]
      · simp; ring
      · intro b' _ hne; simp [hne.symm]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · intro a' _ hne; apply Finset.sum_eq_zero; intro b' _; simp [hne.symm]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · rw [Nat.choose_eq_zero_of_lt (n := b1) (k := b0) (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
      apply Finset.sum_eq_zero; intro a' _; apply Finset.sum_eq_zero; intro b' hb'
      have := Finset.mem_range.mp hb'; simp [show b0 ≠ b' by omega]
    · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a0) (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
      apply Finset.sum_eq_zero; intro a' ha'; apply Finset.sum_eq_zero; intro b' _
      have := Finset.mem_range.mp ha'; simp [show a0 ≠ a' by omega]
    · rw [Nat.choose_eq_zero_of_lt (n := a1) (k := a0) (by omega)]; simp only [Nat.cast_zero, zero_mul, mul_zero]
      apply Finset.sum_eq_zero; intro a' ha'; apply Finset.sum_eq_zero; intro b' _
      have := Finset.mem_range.mp ha'; simp [show a0 ≠ a' by omega]
  -- Evaluate NF at all 7 index families!
  -- (1) idx = (0, 1, a0, b0) (a0 + b0 < k) => A1 a0 b0 = 0
  have hA1_zero : ∀ a0 b0, a0 + b0 < k → A1 a0 b0 = 0 := by
    intro a0 b0 hlt
    let idx : LocalBasisIdx k 2 := ⟨(0, 1, a0, b0),
      (mem_localBasisFinset_iff k 2 0 1 a0 b0).mpr ⟨by omega, by omega, Or.inl (by omega)⟩⟩
    rw [← hNF0 idx]; dsimp [A1, binomWt]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
    unfold kerDLocalNF; dsimp only
    rcases (show (k1=0∧r1=0)∨(k1=1∧r1=0)∨(k1=2∧r1=0)∨(k1=0∧r1=1)∨(k1=1∧r1=1) by omega) with
      ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp only [zero_ne_one, false_and, ↓reduceIte, hred_lt2 0 0 _ _ idx (by omega), idx,
        Prod.mk.injEq, one_ne_zero, and_false, Nat.cast_zero, mul_zero, Finset.sum_const_zero]
    · simp only [true_and, ↓reduceIte, hred_lt2 0 1 _ _ idx (by omega), idx, Prod.mk.injEq]
      have h1 := hsum_single_ab a1 b1 a0 b0 (1 : F)
      simp only [one_mul, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at h1 ⊢
      rw [h1]; ring
    · simp only [show (2:ℕ) ≠ 1 by omega, show (2:ℕ) ≠ 0 by omega, false_and, ↓reduceIte]
      symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a' _; apply Finset.sum_eq_zero; intro b' _
      rw [hred_j2]; cases a' <;> simp [idx]
    · simp only [zero_ne_one, false_and, true_and, ↓reduceIte,
        hred_lt2 0 0 _ _ idx (by omega), hred_lt2 0 1 _ _ idx (by omega), hred_lt2 1 0 _ _ idx (by omega),
        idx, Prod.mk.injEq, one_ne_zero, Nat.cast_zero, mul_zero, zero_add, add_zero, Nat.cast_ite, Nat.cast_one]
      have h1 := hsum_single_ab a1 b1 a0 b0 x0
      have hrew : ∀ a' b', x0 * (if a0 = a' ∧ b0 = b' then (1 : F) else 0) =
          if a0 = a' ∧ b0 = b' then x0 else 0 := fun a' b' => by split_ifs <;> ring
      simp_rw [hrew]; rw [h1]; ring
    · simp only [one_ne_zero, and_false, false_and, true_and, ↓reduceIte]
      have h0 : ∀ a' b', reduceMonomialCoords k 2 0 2 a' b' idx = 0 := fun a' b' => by
        rw [hred_j2]; cases a' <;> simp [idx]
      simp_rw [hred_lt2 0 1 _ _ idx (by omega), h0, hred_lt2 1 1 _ _ idx (by omega)]
      simp only [idx, Prod.mk.injEq, true_and, zero_ne_one, false_and, ↓reduceIte,
        Nat.cast_zero, mul_zero, add_zero, Nat.cast_ite, Nat.cast_one]
      have h1 := hsum_single_ab a1 b1 a0 b0 y0
      have hrew : ∀ a' b', y0 * (if a0 = a' ∧ b0 = b' then (1 : F) else 0) =
          if a0 = a' ∧ b0 = b' then y0 else 0 := fun a' b' => by split_ifs <;> ring
      simp_rw [hrew]; rw [h1]; ring
  -- (2) idx = (1, 0, a0, b0) (1 + a0 + b0 < k) => C0 a0 b0 = 0
  have hC0_zero : ∀ a0 b0, a0 + b0 + 1 < k → C0 a0 b0 = 0 := by
    intro a0 b0 hlt
    let idx : LocalBasisIdx k 2 := ⟨(1, 0, a0, b0),
      (mem_localBasisFinset_iff k 2 1 0 a0 b0).mpr ⟨by omega, by omega, Or.inl (by omega)⟩⟩
    rw [← hNF0 idx]; dsimp [C0, binomWt]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
    unfold kerDLocalNF; dsimp only
    rcases (show (k1=0∧r1=0)∨(k1=1∧r1=0)∨(k1=2∧r1=0)∨(k1=0∧r1=1)∨(k1=1∧r1=1) by omega) with
      ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp [hred_lt2 0 0 _ _ idx (by omega), idx]
    · simp [hred_lt2 0 1 _ _ idx (by omega), idx]
    · simp only [show (2:ℕ) ≠ 0 by omega, false_and, ↓reduceIte]
      symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a' _; apply Finset.sum_eq_zero; intro b' _
      rw [hred_j2]; cases a' <;> simp [idx]
    · simp only [true_and, ↓reduceIte,
        hred_lt2 0 0 _ _ idx (by omega), hred_lt2 0 1 _ _ idx (by omega), hred_lt2 1 0 _ _ idx (by omega),
        idx, Prod.mk.injEq, one_ne_zero, false_and, Nat.cast_zero, mul_zero, zero_add, Nat.cast_ite, Nat.cast_one]
      have h1 := hsum_single_ab a1 b1 a0 b0 (1 : F)
      simp only [one_mul] at h1; rw [h1]; ring
    · simp only [one_ne_zero, false_and, ↓reduceIte]
      symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a' _; apply Finset.sum_eq_zero; intro b' _
      have h0 : reduceMonomialCoords k 2 0 2 a' b' idx = 0 := by rw [hred_j2]; cases a' <;> simp [idx]
      rw [hred_lt2 0 1 _ _ idx (by omega), h0, hred_lt2 1 1 _ _ idx (by omega)]; simp [idx]
  -- (3) idx = (1, 1, a0, b0) (1 + a0 + b0 < k) => C1 a0 b0 = 0
  have hC1_zero : ∀ a0 b0, a0 + b0 + 1 < k → C1 a0 b0 = 0 := by
    intro a0 b0 hlt
    let idx : LocalBasisIdx k 2 := ⟨(1, 1, a0, b0),
      (mem_localBasisFinset_iff k 2 1 1 a0 b0).mpr ⟨by omega, by omega, Or.inl (by omega)⟩⟩
    rw [← hNF0 idx]; dsimp [C1, binomWt]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
    unfold kerDLocalNF; dsimp only
    rcases (show (k1=0∧r1=0)∨(k1=1∧r1=0)∨(k1=2∧r1=0)∨(k1=0∧r1=1)∨(k1=1∧r1=1) by omega) with
      ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp [hred_lt2 0 0 _ _ idx (by omega), idx]
    · simp [hred_lt2 0 1 _ _ idx (by omega), idx]
    · simp only [show (2:ℕ) ≠ 1 by omega, false_and, ↓reduceIte]
      symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a' _; apply Finset.sum_eq_zero; intro b' _
      rw [hred_j2]; cases a' <;> simp [idx]
    · simp [hred_lt2 0 0 _ _ idx (by omega), hred_lt2 0 1 _ _ idx (by omega), hred_lt2 1 0 _ _ idx (by omega), idx]
    · simp only [true_and, ↓reduceIte]
      have h0 : ∀ a' b', reduceMonomialCoords k 2 0 2 a' b' idx = 0 := fun a' b' => by
        rw [hred_j2]; cases a' <;> simp [idx]
      simp_rw [hred_lt2 0 1 _ _ idx (by omega), h0, hred_lt2 1 1 _ _ idx (by omega)]
      simp only [idx, Prod.mk.injEq, one_ne_zero, false_and, true_and, ↓reduceIte,
        Nat.cast_zero, mul_zero, zero_add, Nat.cast_ite, Nat.cast_one]
      have h1 := hsum_single_ab a1 b1 a0 b0 (1 : F)
      simp only [one_mul] at h1; rw [h1]; ring
  -- (4) idx = (0, 2, 0, b0) (b0 < k) => A2 0 b0 = 0
  have hA2_0_zero : ∀ b0, b0 < k → A2 0 b0 = 0 := by
    intro b0 hlt
    let idx : LocalBasisIdx k 2 := ⟨(0, 2, 0, b0),
      (mem_localBasisFinset_iff k 2 0 2 0 b0).mpr ⟨by omega, by omega, Or.inr rfl⟩⟩
    rw [← hNF0 idx]; dsimp [A2, binomWt]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
    unfold kerDLocalNF; dsimp only
    rcases (show (k1=0∧r1=0)∨(k1=1∧r1=0)∨(k1=2∧r1=0)∨(k1=0∧r1=1)∨(k1=1∧r1=1) by omega) with
      ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp [hred_lt2 0 0 _ _ idx (by omega), idx]
    · simp [hred_lt2 0 1 _ _ idx (by omega), idx]
    · simp only [true_and, false_and, and_false, zero_ne_one, one_ne_zero,
        show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, show (0:ℕ) ≠ 2 by omega, show (1:ℕ) ≠ 2 by omega, ↓reduceIte]
      have h2 : ∀ a' b', ((reduceMonomialCoords k 2 0 2 a' b' idx : ℕ) : F) =
          if 0 = a' ∧ b0 = b' then 1 else 0 := fun a' b' => by
        rw [hred_j2]; cases a' with
        | zero => simp [idx]
        | succ a'' =>
            simp only [idx, Prod.mk.injEq, show (0:ℕ) ≠ 2 by omega, show (2:ℕ) ≠ 0 by omega,
              Nat.zero_ne_add_one, false_and, and_false, ↓reduceIte, Nat.cast_zero]
            split_ifs <;> simp
      simp_rw [h2]; have h1 := hsum_single_ab a1 b1 0 b0 (1 : F)
      simp only [one_mul] at h1; rw [h1]; simp only [Nat.choose_zero_right, Nat.sub_zero, ← pow_mul, mul_comm 2 _]; ring
    · simp [hred_lt2 0 0 _ _ idx (by omega), hred_lt2 0 1 _ _ idx (by omega), hred_lt2 1 0 _ _ idx (by omega), idx]
    · simp only [true_and, false_and, and_false, zero_ne_one, one_ne_zero,
        show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, show (0:ℕ) ≠ 2 by omega, show (1:ℕ) ≠ 2 by omega, ↓reduceIte]
      have h2 : ∀ a' b', ((reduceMonomialCoords k 2 0 2 a' b' idx : ℕ) : F) =
          if 0 = a' ∧ b0 = b' then 1 else 0 := fun a' b' => by
        rw [hred_j2]; cases a' with
        | zero => simp [idx]
        | succ a'' =>
            simp only [idx, Prod.mk.injEq, show (0:ℕ) ≠ 2 by omega, show (2:ℕ) ≠ 0 by omega,
              Nat.zero_ne_add_one, false_and, and_false, ↓reduceIte, Nat.cast_zero]
            split_ifs <;> simp
      simp_rw [hred_lt2 0 1 _ _ idx (by omega), h2, hred_lt2 1 1 _ _ idx (by omega)]
      simp only [idx, Prod.mk.injEq, show (2:ℕ) ≠ 1 by omega, zero_ne_one, one_ne_zero, false_and, and_false, ↓reduceIte,
        Nat.cast_zero, mul_zero, zero_add, add_zero]
      have hrew : ∀ a' b', x0 * (if 0 = a' ∧ b0 = b' then (1 : F) else 0) =
          if 0 = a' ∧ b0 = b' then x0 else 0 := fun a' b' => by split_ifs <;> ring
      simp_rw [hrew]; rw [hsum_single_ab a1 b1 0 b0 x0]; simp only [Nat.choose_zero_right, Nat.sub_zero, ← pow_mul, mul_comm 2 _]; ring
  -- (5) idx = (2, 0, a0, b0) (2 + a0 + b0 < k) => A2 (a0 + 1) b0 = 0
  have hA2_succ_zero : ∀ a0 b0, a0 + b0 + 2 < k → A2 (a0 + 1) b0 = 0 := by
    intro a0 b0 hlt
    let idx : LocalBasisIdx k 2 := ⟨(2, 0, a0, b0),
      (mem_localBasisFinset_iff k 2 2 0 a0 b0).mpr ⟨by omega, by omega, Or.inl (by omega)⟩⟩
    rw [← hNF0 idx]; dsimp [A2, binomWt]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
    unfold kerDLocalNF; dsimp only
    rcases (show (k1=0∧r1=0)∨(k1=1∧r1=0)∨(k1=2∧r1=0)∨(k1=0∧r1=1)∨(k1=1∧r1=1) by omega) with
      ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp [hred_lt2 0 0 _ _ idx (by omega), idx]
    · simp [hred_lt2 0 1 _ _ idx (by omega), idx]
    · simp only [true_and, ↓reduceIte]
      have h2 : ∀ a' b', ((reduceMonomialCoords k 2 0 2 a' b' idx : ℕ) : F) =
          if a0 + 1 = a' ∧ b0 = b' then 1 else 0 := fun a' b' => by
        rw [hred_j2]; cases a' with
        | zero => simp [idx]
        | succ a'' =>
            simp only [idx, Prod.mk.injEq, show (2:ℕ) ≠ 0 by omega, false_and, ↓reduceIte, zero_add,
              Nat.add_right_cancel_iff]
            by_cases heq : a0 = a'' ∧ b0 = b'
            · rcases heq with ⟨rfl, rfl⟩; simp [show a0 + 1 + b0 < k by omega]
            · split_ifs <;> simp_all
      simp_rw [h2]; have h1 := hsum_single_ab a1 b1 (a0 + 1) b0 (1 : F)
      simp only [one_mul] at h1; rw [h1]; ring
    · simp [hred_lt2 0 0 _ _ idx (by omega), hred_lt2 0 1 _ _ idx (by omega), hred_lt2 1 0 _ _ idx (by omega), idx]
    · simp only [true_and, false_and, and_false, zero_ne_one, one_ne_zero,
        show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, show (0:ℕ) ≠ 2 by omega, show (1:ℕ) ≠ 2 by omega, ↓reduceIte]
      have h2 : ∀ a' b', ((reduceMonomialCoords k 2 0 2 a' b' idx : ℕ) : F) =
          if a0 + 1 = a' ∧ b0 = b' then 1 else 0 := fun a' b' => by
        rw [hred_j2]; cases a' with
        | zero => simp [idx]
        | succ a'' =>
            simp only [idx, Prod.mk.injEq, show (2:ℕ) ≠ 0 by omega, false_and, ↓reduceIte, zero_add,
              Nat.add_right_cancel_iff]
            by_cases heq : a0 = a'' ∧ b0 = b'
            · rcases heq with ⟨rfl, rfl⟩; simp [show a0 + 1 + b0 < k by omega]
            · split_ifs <;> simp_all
      simp_rw [hred_lt2 0 1 _ _ idx (by omega), h2, hred_lt2 1 1 _ _ idx (by omega)]
      simp only [idx, Prod.mk.injEq, show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, zero_ne_one, one_ne_zero,
        false_and, and_false, ↓reduceIte, Nat.cast_zero, mul_zero, zero_add, add_zero]
      have hrew : ∀ a' b', x0 * (if a0 + 1 = a' ∧ b0 = b' then (1 : F) else 0) =
          if a0 + 1 = a' ∧ b0 = b' then x0 else 0 := fun a' b' => by split_ifs <;> ring
      simp_rw [hrew]; rw [hsum_single_ab a1 b1 (a0 + 1) b0 x0]; ring
  -- (6) idx = (0, 0, a0, 0) (a0 < k) => A0 a0 0 = 0
  have hA0_0_zero : ∀ a0, a0 < k → A0 a0 0 = 0 := by
    intro a0 hlt
    let idx : LocalBasisIdx k 2 := ⟨(0, 0, a0, 0),
      (mem_localBasisFinset_iff k 2 0 0 a0 0).mpr ⟨by omega, by omega, Or.inl (by omega)⟩⟩
    rw [← hNF0 idx]; dsimp [A0, binomWt]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
    unfold kerDLocalNF; dsimp only
    rcases (show (k1=0∧r1=0)∨(k1=1∧r1=0)∨(k1=2∧r1=0)∨(k1=0∧r1=1)∨(k1=1∧r1=1) by omega) with
      ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp only [true_and, false_and, and_false, zero_ne_one, one_ne_zero, ↓reduceIte,
        hred_lt2 0 0 _ _ idx (by omega), idx, Prod.mk.injEq,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      have h1 := hsum_single_ab a1 b1 a0 0 (1 : F); simp only [one_mul] at h1; rw [h1]
      simp only [Nat.choose_zero_right, Nat.sub_zero, ← pow_mul, mul_comm 2 _]; ring
    · simp [hred_lt2 0 1 _ _ idx (by omega), idx]
    · simp only [show (2:ℕ) ≠ 0 by omega, false_and, ↓reduceIte]
      symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a' _; apply Finset.sum_eq_zero; intro b' _
      rw [hred_j2]; cases a' with
      | zero => simp [idx]
      | succ a'' =>
          simp only [idx, Prod.mk.injEq, show (0:ℕ) ≠ 2 by omega, Nat.zero_ne_add_one,
            false_and, and_false, ↓reduceIte, Nat.cast_zero]
          split_ifs <;> simp
    · simp only [true_and, zero_ne_one, one_ne_zero, and_false, false_and, ↓reduceIte,
        hred_lt2 0 0 _ _ idx (by omega), hred_lt2 0 1 _ _ idx (by omega), hred_lt2 1 0 _ _ idx (by omega),
        idx, Prod.mk.injEq, Nat.cast_zero, mul_zero, add_zero, Nat.cast_ite, Nat.cast_one]
      have hrew : ∀ a' b', y0 * (if a0 = a' ∧ 0 = b' then (1 : F) else 0) =
          if a0 = a' ∧ 0 = b' then y0 else 0 := fun a' b' => by split_ifs <;> ring
      simp_rw [hrew]; rw [hsum_single_ab a1 b1 a0 0 y0]
      simp only [Nat.choose_zero_right, Nat.sub_zero, ← pow_mul, mul_comm 2 _]; ring
    · simp only [one_ne_zero, false_and, ↓reduceIte]
      symm; rw [mul_eq_zero]; right; apply Finset.sum_eq_zero; intro a' _; apply Finset.sum_eq_zero; intro b' _
      have h2 : reduceMonomialCoords k 2 0 2 a' b' idx = 0 := by
        rw [hred_j2]; cases a' with
        | zero => simp [idx]
        | succ a'' =>
            simp only [idx, Prod.mk.injEq, show (0:ℕ) ≠ 2 by omega, Nat.zero_ne_add_one,
              false_and, and_false, ↓reduceIte]
            split_ifs <;> simp
      rw [hred_lt2 0 1 _ _ idx (by omega), h2, hred_lt2 1 1 _ _ idx (by omega)]; simp [idx]
  -- (7) idx = (0, 0, a0, b0 + 1) (a0 + b0 + 1 < k) => A0 a0 (b0 + 1) + A2 (a0 + 1) b0 = 0!!
  have hA0A2_zero : ∀ a0 b0, a0 + b0 + 1 < k → A0 a0 (b0 + 1) + A2 (a0 + 1) b0 = 0 := by
    intro a0 b0 hlt
    let idx : LocalBasisIdx k 2 := ⟨(0, 0, a0, b0 + 1),
      (mem_localBasisFinset_iff k 2 0 0 a0 (b0 + 1)).mpr ⟨by omega, by omega, Or.inl (by omega)⟩⟩
    rw [← hNF0 idx]; dsimp [A0, A2, binomWt]; rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
    have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
    unfold kerDLocalNF; dsimp only
    have h2 : ∀ a' b', ((reduceMonomialCoords k 2 0 2 a' b' idx : ℕ) : F) =
        if a0 + 1 = a' ∧ b0 = b' then 1 else 0 := fun a' b' => by
      rw [hred_j2]; cases a' with
      | zero => simp [idx]
      | succ a'' =>
          simp only [idx, Prod.mk.injEq, show (0:ℕ) ≠ 2 by omega, false_and, ↓reduceIte, add_zero,
            Nat.add_right_cancel_iff]
          by_cases heq : a0 = a'' ∧ b0 = b'
          · rcases heq with ⟨rfl, rfl⟩; simp [show a0 + 1 + b0 < k by omega]
          · split_ifs <;> simp_all
    rcases (show (k1=0∧r1=0)∨(k1=1∧r1=0)∨(k1=2∧r1=0)∨(k1=0∧r1=1)∨(k1=1∧r1=1) by omega) with
      ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp only [true_and, show (0:ℕ) ≠ 2 by omega, zero_ne_one, one_ne_zero, false_and, and_false, ↓reduceIte, add_zero,
        hred_lt2 0 0 _ _ idx (by omega), idx, Prod.mk.injEq, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      have h1 := hsum_single_ab a1 b1 a0 (b0 + 1) (1 : F); simp only [one_mul] at h1; rw [h1]; ring
    · simp [hred_lt2 0 1 _ _ idx (by omega), idx]
    · simp only [show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega, false_and, true_and, ↓reduceIte, zero_add]
      simp_rw [h2]; have h1 := hsum_single_ab a1 b1 (a0 + 1) b0 (1 : F)
      simp only [one_mul] at h1; rw [h1]; ring
    · simp only [true_and, show (0:ℕ) ≠ 2 by omega, zero_ne_one, one_ne_zero, false_and, and_false, ↓reduceIte, add_zero,
        hred_lt2 0 0 _ _ idx (by omega), hred_lt2 0 1 _ _ idx (by omega), hred_lt2 1 0 _ _ idx (by omega),
        idx, Prod.mk.injEq, Nat.cast_zero, mul_zero, Nat.cast_ite, Nat.cast_one]
      have hrew : ∀ a' b', y0 * (if a0 = a' ∧ b0 + 1 = b' then (1 : F) else 0) =
          if a0 = a' ∧ b0 + 1 = b' then y0 else 0 := fun a' b' => by split_ifs <;> ring
      simp_rw [hrew]; rw [hsum_single_ab a1 b1 a0 (b0 + 1) y0]; ring
    · simp only [one_ne_zero, zero_ne_one, show (1:ℕ) ≠ 2 by omega, false_and, and_false, true_and, ↓reduceIte, zero_add]
      simp_rw [hred_lt2 0 1 _ _ idx (by omega), h2, hred_lt2 1 1 _ _ idx (by omega)]
      simp only [idx, Prod.mk.injEq, zero_ne_one, one_ne_zero, false_and, and_false, ↓reduceIte, Nat.cast_zero, mul_zero, zero_add, add_zero]
      have hrew : ∀ a' b', x0 * (if a0 + 1 = a' ∧ b0 = b' then (1 : F) else 0) =
          if a0 + 1 = a' ∧ b0 = b' then x0 else 0 := fun a' b' => by split_ifs <;> ring
      simp_rw [hrew]; rw [hsum_single_ab a1 b1 (a0 + 1) b0 x0]; ring
  -- Consequence: A0 a0 b0 = 0 for a0 + b0 + 1 < k!
  have hA0_zero : ∀ a0 b0, a0 + b0 + 1 < k → A0 a0 b0 = 0 := by
    intro a0 b0 hlt
    cases b0 with
    | zero => exact hA0_0_zero a0 (by omega)
    | succ b0' =>
        have hsum := hA0A2_zero a0 b0' (by omega)
        have hA2 := hA2_succ_zero a0 b0' (by omega)
        rw [hA2, add_zero] at hsum; exact hsum
  -- Step 2: Explicit shiftBi formulas for f0, f1, f2!
  have hshift_f0 : ∀ i j, ((shiftBi x0 y0 (Fpoly.coeff 0)).coeff j).coeff i =
      if i % 2 = 0 ∧ j % 2 = 0 then A0 (i / 2) (j / 2)
      else if i % 2 = 0 ∧ j % 2 = 1 then C0 (i / 2) (j / 2) else 0 := by
    intro i j
    have hf0 : Fpoly.coeff 0 = ∑ e : KerDIdx wY W_F 2,
        if e.1.1 = 0 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 0 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else 0 := by
      dsimp [Fpoly]; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
      have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
      rcases (show (k1=0∧r1=0)∨(k1=1∧r1=0)∨(k1=2∧r1=0)∨(k1=0∧r1=1)∨(k1=1∧r1=1) by omega) with
        ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · simp only [true_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_zero, one_mul, one_mul,
          show C (C (C (f_coord ⟨(0,0,b1,a1),he⟩))) * ((C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0,0,b1,a1),he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow]; ring,
          coeff_C, if_pos rfl]
      · simp only [one_ne_zero, false_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_one, pow_zero, mul_one,
          show ∀ (p q r : ContactPoly F), p * (X * q * r) = X * (p * q * r) by intros; ring, coeff_X_mul_zero]
      · simp only [show (2:ℕ) ≠ 0 by omega, false_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, mul_one, sq,
          show ∀ (p q r : ContactPoly F), p * (X * X * q * r) = X * (p * X * q * r) by intros; ring, coeff_X_mul_zero]
      · simp only [zero_ne_one, one_ne_zero, and_false, false_and, true_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_one, one_mul,
          show C (C (C (f_coord ⟨(0,1,b1,a1),he⟩))) * ((C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0,1,b1,a1),he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
            X * C (C (C (f_coord ⟨(0,1,b1,a1),he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow]; ring,
          coeff_add, coeff_C, if_pos rfl, coeff_X_mul_zero, add_zero]
      · simp only [one_ne_zero, false_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_one, pow_one,
          show ∀ (p q r s : ContactPoly F), p * (X * q * r * s) = X * (p * q * r * s) by intros; ring, coeff_X_mul_zero]
    rw [hf0, shiftBi_sum, finset_sum_coeff, finset_sum_coeff]
    have hR : (if i % 2 = 0 ∧ j % 2 = 0 then A0 (i / 2) (j / 2)
        else if i % 2 = 0 ∧ j % 2 = 1 then C0 (i / 2) (j / 2) else 0) =
        ∑ e : KerDIdx wY W_F 2,
          if e.1.1 = 0 ∧ e.1.2.1 = 0 then (if i % 2 = 0 ∧ j % 2 = 0 then binomWt e (i / 2) (j / 2) else 0)
          else if e.1.1 = 0 ∧ e.1.2.1 = 1 then
            (if i % 2 = 0 ∧ j % 2 = 0 then y0 * binomWt e (i / 2) (j / 2)
             else if i % 2 = 0 ∧ j % 2 = 1 then binomWt e (i / 2) (j / 2) else 0)
          else 0 := by
      dsimp [A0, C0]; split_ifs <;> first
        | (apply Finset.sum_congr rfl; intro e _; split_ifs <;> first | rfl | omega)
        | (symm; apply Finset.sum_eq_zero; intro e _; split_ifs <;> first | rfl | omega)
    rw [hR]; apply Finset.sum_congr rfl; intro e _
    have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
    rcases (show (e.1.1=0∧e.1.2.1=0)∨(e.1.1=1∧e.1.2.1=0)∨(e.1.1=2∧e.1.2.1=0)∨(e.1.1=0∧e.1.2.1=1)∨(e.1.1=1∧e.1.2.1=1) by omega) with
      ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩
    · simp only [h1, h2, true_and, ↓reduceIte]
      simpa [binomWt] using shiftBi_monom_even x0 y0 (f_coord e) e.1.2.2.2 e.1.2.2.1 i j
    · simp only [h1, h2, one_ne_zero, zero_ne_one, false_and, and_false, ↓reduceIte]; unfold shiftBi; simp
    · simp only [h1, h2, show (2:ℕ) ≠ 0 by omega, false_and, ↓reduceIte]; unfold shiftBi; simp
    · simp only [h1, h2, one_ne_zero, zero_ne_one, and_false, true_and, ↓reduceIte]
      rw [shiftBi_monom_Y_mul_even]; dsimp [binomWt]; split_ifs <;> ring
    · simp only [h1, h2, one_ne_zero, false_and, ↓reduceIte]; unfold shiftBi; simp
  have hshift_f1 : ∀ i j, ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff j).coeff i =
      if i % 2 = 0 ∧ j % 2 = 0 then A1 (i / 2) (j / 2)
      else if i % 2 = 1 ∧ j % 2 = 0 then C0 (i / 2) (j / 2)
      else if i % 2 = 0 ∧ j % 2 = 1 then C1 (i / 2) (j / 2) else 0 := by
    intro i j
    have hf1 : Fpoly.coeff 1 = ∑ e : KerDIdx wY W_F 2,
        if e.1.1 = 1 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 0 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * C X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 1 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else 0 := by
      dsimp [Fpoly]; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
      have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
      rcases (show (k1=0∧r1=0)∨(k1=1∧r1=0)∨(k1=2∧r1=0)∨(k1=0∧r1=1)∨(k1=1∧r1=1) by omega) with
        ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · simp only [zero_ne_one, one_ne_zero, false_and, and_false, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_zero, one_mul, one_mul,
          show C (C (C (f_coord ⟨(0,0,b1,a1),he⟩))) * ((C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0,0,b1,a1),he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow]; ring,
          coeff_C, if_neg one_ne_zero]
      · simp only [true_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_one, pow_zero, mul_one,
          show C (C (C (f_coord ⟨(1,0,b1,a1),he⟩))) * (X * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            X * C (C (C (f_coord ⟨(1,0,b1,a1),he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow]; ring,
          coeff_X_mul, coeff_C, if_pos rfl]
      · simp only [show (2:ℕ) ≠ 1 by omega, show (2:ℕ) ≠ 0 by omega, false_and, ↓reduceIte]
        unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, mul_one, sq,
          show ∀ (p q r : ContactPoly F), p * (X * X * q * r) = X * (X * (p * q * r)) by intros; ring,
          coeff_X_mul, coeff_X_mul_zero]
      · simp only [zero_ne_one, false_and, true_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_one, one_mul,
          show C (C (C (f_coord ⟨(0,1,b1,a1),he⟩))) * ((C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0,1,b1,a1),he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
            X * C (C (C (f_coord ⟨(0,1,b1,a1),he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow]; ring,
          coeff_add, coeff_C, if_neg one_ne_zero, zero_add, coeff_X_mul, coeff_C, if_pos rfl]
      · simp only [one_ne_zero, and_false, false_and, true_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_one, pow_one,
          show C (C (C (f_coord ⟨(1,1,b1,a1),he⟩))) * (X * (C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            X * C (C (C (f_coord ⟨(1,1,b1,a1),he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
            X * (X * C (C (C (f_coord ⟨(1,1,b1,a1),he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1)) by
          simp only [map_mul, map_pow]; ring,
          coeff_add, coeff_X_mul, coeff_C, if_pos rfl, coeff_X_mul, coeff_X_mul_zero, add_zero]
    rw [hf1, shiftBi_sum, finset_sum_coeff, finset_sum_coeff]
    have hR : (if i % 2 = 0 ∧ j % 2 = 0 then A1 (i / 2) (j / 2)
        else if i % 2 = 1 ∧ j % 2 = 0 then C0 (i / 2) (j / 2)
        else if i % 2 = 0 ∧ j % 2 = 1 then C1 (i / 2) (j / 2) else 0) =
        ∑ e : KerDIdx wY W_F 2,
          if e.1.1 = 1 ∧ e.1.2.1 = 0 then (if i % 2 = 0 ∧ j % 2 = 0 then binomWt e (i / 2) (j / 2) else 0)
          else if e.1.1 = 0 ∧ e.1.2.1 = 1 then
            (if i % 2 = 0 ∧ j % 2 = 0 then x0 * binomWt e (i / 2) (j / 2)
             else if i % 2 = 1 ∧ j % 2 = 0 then binomWt e (i / 2) (j / 2) else 0)
          else if e.1.1 = 1 ∧ e.1.2.1 = 1 then
            (if i % 2 = 0 ∧ j % 2 = 0 then y0 * binomWt e (i / 2) (j / 2)
             else if i % 2 = 0 ∧ j % 2 = 1 then binomWt e (i / 2) (j / 2) else 0)
          else 0 := by
      dsimp [A1, C0, C1]; split_ifs <;> first
        | (apply Finset.sum_congr rfl; intro e _; split_ifs <;> first | rfl | omega)
        | (symm; apply Finset.sum_eq_zero; intro e _; split_ifs <;> first | rfl | omega)
    rw [hR]; apply Finset.sum_congr rfl; intro e _
    have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
    rcases (show (e.1.1=0∧e.1.2.1=0)∨(e.1.1=1∧e.1.2.1=0)∨(e.1.1=2∧e.1.2.1=0)∨(e.1.1=0∧e.1.2.1=1)∨(e.1.1=1∧e.1.2.1=1) by omega) with
      ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩
    · simp only [h1, h2, zero_ne_one, one_ne_zero, false_and, and_false, ↓reduceIte]; unfold shiftBi; simp
    · simp only [h1, h2, true_and, ↓reduceIte]
      simpa [binomWt] using shiftBi_monom_even x0 y0 (f_coord e) e.1.2.2.2 e.1.2.2.1 i j
    · simp only [h1, h2, show (2:ℕ) ≠ 1 by omega, show (2:ℕ) ≠ 0 by omega, false_and, ↓reduceIte]; unfold shiftBi; simp
    · simp only [h1, h2, zero_ne_one, one_ne_zero, false_and, true_and, ↓reduceIte]
      rw [shiftBi_monom_X_mul_even]; dsimp [binomWt]; split_ifs <;> ring
    · simp only [h1, h2, one_ne_zero, zero_ne_one, and_false, false_and, true_and, ↓reduceIte]
      rw [shiftBi_monom_Y_mul_even]; dsimp [binomWt]; split_ifs <;> ring
  have hshift_f2 : ∀ i j, ((shiftBi x0 y0 (Fpoly.coeff 2)).coeff j).coeff i =
      if i % 2 = 0 ∧ j % 2 = 0 then A2 (i / 2) (j / 2)
      else if i % 2 = 1 ∧ j % 2 = 0 then C1 (i / 2) (j / 2) else 0 := by
    intro i j
    have hf2 : Fpoly.coeff 2 = ∑ e : KerDIdx wY W_F 2,
        if e.1.1 = 2 ∧ e.1.2.1 = 0 then C (C (f_coord e)) * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else if e.1.1 = 1 ∧ e.1.2.1 = 1 then C (C (f_coord e)) * C X * C (X ^ 2) ^ e.1.2.2.2 * (X ^ 2) ^ e.1.2.2.1
        else 0 := by
      dsimp [Fpoly]; rw [finset_sum_coeff]; apply Finset.sum_congr rfl; intro ⟨⟨k1, r1, b1, a1⟩, he⟩ _
      have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
      rcases (show (k1=0∧r1=0)∨(k1=1∧r1=0)∨(k1=2∧r1=0)∨(k1=0∧r1=1)∨(k1=1∧r1=1) by omega) with
        ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · simp only [show (0:ℕ) ≠ 2 by omega, zero_ne_one, false_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_zero, one_mul, one_mul,
          show C (C (C (f_coord ⟨(0,0,b1,a1),he⟩))) * ((C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0,0,b1,a1),he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow]; ring,
          coeff_C, if_neg (by omega)]
      · simp only [show (1:ℕ) ≠ 2 by omega, zero_ne_one, false_and, and_false, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_one, pow_zero, mul_one,
          show C (C (C (f_coord ⟨(1,0,b1,a1),he⟩))) * (X * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            X * C (C (C (f_coord ⟨(1,0,b1,a1),he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow]; ring,
          coeff_X_mul, coeff_C, if_neg one_ne_zero]
      · simp only [true_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, mul_one, sq,
          show C (C (C (f_coord ⟨(2,0,b1,a1),he⟩))) * (X * X * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            X * (X * C (C (C (f_coord ⟨(2,0,b1,a1),he⟩)) * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1)) by
          simp only [map_mul, map_pow]; ring,
          coeff_X_mul, coeff_X_mul, coeff_C, if_pos rfl]
      · simp only [show (0:ℕ) ≠ 2 by omega, zero_ne_one, false_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_zero, pow_one, one_mul,
          show C (C (C (f_coord ⟨(0,1,b1,a1),he⟩))) * ((C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            C (C (C (f_coord ⟨(0,1,b1,a1),he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
            X * C (C (C (f_coord ⟨(0,1,b1,a1),he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) by simp only [map_mul, map_pow]; ring,
          coeff_add, coeff_C, if_neg (by omega), zero_add, coeff_X_mul, coeff_C, if_neg one_ne_zero]
      · simp only [show (1:ℕ) ≠ 2 by omega, false_and, true_and, ↓reduceIte]; unfold kerDBasisPoly cC cR cY cX; dsimp only
        rw [pow_one, pow_one,
          show C (C (C (f_coord ⟨(1,1,b1,a1),he⟩))) * (X * (C X + C (C X) * X) * (C (C X) ^ 2) ^ a1 * (C X ^ 2) ^ b1) =
            X * C (C (C (f_coord ⟨(1,1,b1,a1),he⟩)) * X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1) +
            X * (X * C (C (C (f_coord ⟨(1,1,b1,a1),he⟩)) * C X * C (X ^ 2) ^ a1 * (X ^ 2) ^ b1)) by
          simp only [map_mul, map_pow]; ring,
          coeff_add, coeff_X_mul, coeff_C, if_neg one_ne_zero, zero_add, coeff_X_mul, coeff_X_mul, coeff_C, if_pos rfl]
    rw [hf2, shiftBi_sum, finset_sum_coeff, finset_sum_coeff]
    have hR : (if i % 2 = 0 ∧ j % 2 = 0 then A2 (i / 2) (j / 2)
        else if i % 2 = 1 ∧ j % 2 = 0 then C1 (i / 2) (j / 2) else 0) =
        ∑ e : KerDIdx wY W_F 2,
          if e.1.1 = 2 ∧ e.1.2.1 = 0 then (if i % 2 = 0 ∧ j % 2 = 0 then binomWt e (i / 2) (j / 2) else 0)
          else if e.1.1 = 1 ∧ e.1.2.1 = 1 then
            (if i % 2 = 0 ∧ j % 2 = 0 then x0 * binomWt e (i / 2) (j / 2)
             else if i % 2 = 1 ∧ j % 2 = 0 then binomWt e (i / 2) (j / 2) else 0)
          else 0 := by
      dsimp [A2, C1]; split_ifs <;> first
        | (apply Finset.sum_congr rfl; intro e _; split_ifs <;> first | rfl | omega)
        | (symm; apply Finset.sum_eq_zero; intro e _; split_ifs <;> first | rfl | omega)
    rw [hR]; apply Finset.sum_congr rfl; intro e _
    have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
    rcases (show (e.1.1=0∧e.1.2.1=0)∨(e.1.1=1∧e.1.2.1=0)∨(e.1.1=2∧e.1.2.1=0)∨(e.1.1=0∧e.1.2.1=1)∨(e.1.1=1∧e.1.2.1=1) by omega) with
      ⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩|⟨h1,h2⟩
    · simp only [h1, h2, show (0:ℕ) ≠ 2 by omega, zero_ne_one, false_and, ↓reduceIte]; unfold shiftBi; simp
    · simp only [h1, h2, show (1:ℕ) ≠ 2 by omega, zero_ne_one, false_and, and_false, ↓reduceIte]; unfold shiftBi; simp
    · simp only [h1, h2, true_and, ↓reduceIte]
      simpa [binomWt] using shiftBi_monom_even x0 y0 (f_coord e) e.1.2.2.2 e.1.2.2.1 i j
    · simp only [h1, h2, show (0:ℕ) ≠ 2 by omega, zero_ne_one, false_and, ↓reduceIte]; unfold shiftBi; simp
    · simp only [h1, h2, show (1:ℕ) ≠ 2 by omega, false_and, true_and, ↓reduceIte]
      rw [shiftBi_monom_X_mul_even]; dsimp [binomWt]; split_ifs <;> ring
  -- Step 3: Read off the three biMultGE bounds!
  have hbm0 : biMultGE x0 y0 (Fpoly.coeff 0) (2 * k - 2) := by
    intro i j hij; rw [hshift_f0]; split_ifs with h1 h2
    · exact hA0_zero (i / 2) (j / 2) (by omega)
    · exact hC0_zero (i / 2) (j / 2) (by omega)
    · rfl
  have hbm1 : biMultGE x0 y0 (Fpoly.coeff 1) (2 * k - 1) := by
    intro i j hij; rw [hshift_f1]; split_ifs with h1 h2 h3
    · exact hA1_zero (i / 2) (j / 2) (by omega)
    · exact hC0_zero (i / 2) (j / 2) (by omega)
    · exact hC1_zero (i / 2) (j / 2) (by omega)
    · rfl
  have hbm2 : biMultGE x0 y0 (Fpoly.coeff 2) (2 * k - 2) := by
    intro i j hij; rw [hshift_f2]; split_ifs with h1 h2
    · cases ha : i / 2 with
      | zero => exact hA2_0_zero (j / 2) (by omega)
      | succ a'' => exact hA2_succ_zero a'' (j / 2) (by omega)
    · exact hC1_zero (i / 2) (j / 2) (by omega)
    · rfl
  -- Step 4: Construct Pe = C (X^2) * A0_poly + X * A2_poly and Po = C X * A1_poly!
  have hshift_deg : ∀ g : BiPoly F, (shiftBi x0 y0 g).natDegree ≤ g.natDegree := by
    intro g; unfold shiftBi
    refine natDegree_comp_le.trans ?_
    have h1 : (g.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ g.natDegree := natDegree_map_le
    have h2 : (C (C y0) + X : BiPoly F).natDegree ≤ 1 := (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
    nlinarith only [h1, h2]
  have hA0_b : ∀ a' b', (Fpoly.coeff 0).natDegree / 2 < b' → A0 a' b' = 0 := by
    intro a' b' hb; have h0 := hshift_f0 (2 * a') (2 * b'); have hle := hshift_deg (Fpoly.coeff 0)
    have hz : (shiftBi x0 y0 (Fpoly.coeff 0)).coeff (2 * b') = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, coeff_zero] at h0; simpa using h0.symm
  have hA1_b : ∀ a' b', (Fpoly.coeff 1).natDegree / 2 < b' → A1 a' b' = 0 := by
    intro a' b' hb; have h0 := hshift_f1 (2 * a') (2 * b'); have hle := hshift_deg (Fpoly.coeff 1)
    have hz : (shiftBi x0 y0 (Fpoly.coeff 1)).coeff (2 * b') = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, coeff_zero] at h0; simpa using h0.symm
  have hA2_b : ∀ a' b', (Fpoly.coeff 2).natDegree / 2 < b' → A2 a' b' = 0 := by
    intro a' b' hb; have h0 := hshift_f2 (2 * a') (2 * b'); have hle := hshift_deg (Fpoly.coeff 2)
    have hz : (shiftBi x0 y0 (Fpoly.coeff 2)).coeff (2 * b') = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz, coeff_zero] at h0; simpa using h0.symm
  have hA_a : ∀ a' b', W_F / 2 < a' → A0 a' b' = 0 ∧ A1 a' b' = 0 ∧ A2 a' b' = 0 := by
    intro a' b' ha
    have hbw : ∀ e : KerDIdx wY W_F 2, binomWt e a' b' = 0 := fun ⟨⟨k1, r1, b1, a1⟩, he⟩ => by
      have hm := (mem_kerDIdxFinset_iff wY W_F 2 hwY k1 r1 b1 a1).mp he
      have ha1 : a1 < a' := by omega
      dsimp [binomWt]; simp [Nat.choose_eq_zero_of_lt ha1]
    exact ⟨Finset.sum_eq_zero fun e _ => by split_ifs <;> simp [hbw e],
      Finset.sum_eq_zero fun e _ => by split_ifs <;> simp [hbw e],
      Finset.sum_eq_zero fun e _ => by split_ifs <;> simp [hbw e]⟩
  have hstep4 : ∀ (A0 A1 A2 C0 C1 : ℕ → ℕ → F),
      (∀ i j, ((shiftBi x0 y0 (Fpoly.coeff 0)).coeff j).coeff i =
        if i % 2 = 0 ∧ j % 2 = 0 then A0 (i / 2) (j / 2)
        else if i % 2 = 0 ∧ j % 2 = 1 then C0 (i / 2) (j / 2) else 0) →
      (∀ i j, ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff j).coeff i =
        if i % 2 = 0 ∧ j % 2 = 0 then A1 (i / 2) (j / 2)
        else if i % 2 = 1 ∧ j % 2 = 0 then C0 (i / 2) (j / 2)
        else if i % 2 = 0 ∧ j % 2 = 1 then C1 (i / 2) (j / 2) else 0) →
      (∀ i j, ((shiftBi x0 y0 (Fpoly.coeff 2)).coeff j).coeff i =
        if i % 2 = 0 ∧ j % 2 = 0 then A2 (i / 2) (j / 2)
        else if i % 2 = 1 ∧ j % 2 = 0 then C1 (i / 2) (j / 2) else 0) →
      (∀ a' b', (Fpoly.coeff 0).natDegree / 2 < b' → A0 a' b' = 0) →
      (∀ a' b', (Fpoly.coeff 1).natDegree / 2 < b' → A1 a' b' = 0) →
      (∀ a' b', (Fpoly.coeff 2).natDegree / 2 < b' → A2 a' b' = 0) →
      (∀ a' b', W_F / 2 < a' → A0 a' b' = 0 ∧ A1 a' b' = 0 ∧ A2 a' b' = 0) →
      (∀ a0, a0 < k → A0 a0 0 = 0) →
      (∀ b0, b0 < k → A2 0 b0 = 0) →
      (∀ a0 b0, a0 + b0 + 1 < k → A0 a0 (b0 + 1) + A2 (a0 + 1) b0 = 0) →
      (∀ a0 b0, a0 + b0 < k → A1 a0 b0 = 0) →
      ∃ Pe Po : BiPoly F,
        shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) +
          shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X) +
          shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2 =
          Polynomial.expand (Polynomial F) 2 Pe + X * Polynomial.expand (Polynomial F) 2 Po ∧
        2 * Pe.natDegree ≤ max (Fpoly.coeff 0).natDegree ((Fpoly.coeff 2).natDegree + 2) ∧
        2 * Po.natDegree ≤ (Fpoly.coeff 1).natDegree ∧
        weightedOrdGE 2 (2 * k + 2) Pe ∧
        weightedOrdGE 2 (2 * k + 1) Po ∧
        weightedOrdGE 2 (4 * k + 4) (Pe ^ 2 + X * Po ^ 2) := by
    intro A0 A1 A2 C0 C1 hshift_f0 hshift_f1 hshift_f2 hA0_b hA1_b hA2_b hA_a hA0_0_zero hA2_0_zero hA0A2_zero hA1_zero
    let Pe : BiPoly F :=
      C (X ^ 2) * mkEvenBi ((Fpoly.coeff 0).natDegree / 2) (W_F / 2) A0 +
      X * mkEvenBi ((Fpoly.coeff 2).natDegree / 2) (W_F / 2) A2
    let Po : BiPoly F :=
      C X * mkEvenBi ((Fpoly.coeff 1).natDegree / 2) (W_F / 2) A1
    have hPe_eq : shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2) +
        shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X) +
        shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2 =
        Polynomial.expand (Polynomial F) 2 Pe + X * Polynomial.expand (Polynomial F) 2 Po := by
      ext j i
      have hL1 : (((shiftBi x0 y0 (Fpoly.coeff 0) * C (X ^ 2)).coeff j).coeff i) =
          if 2 ≤ i then ((shiftBi x0 y0 (Fpoly.coeff 0)).coeff j).coeff (i - 2) else 0 := by
        rw [coeff_mul_C, mul_comm, coeff_X_pow_mul']
      have hL2 : (((shiftBi x0 y0 (Fpoly.coeff 1) * (C X * X)).coeff j).coeff i) =
          if 1 ≤ i ∧ 1 ≤ j then ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff (j - 1)).coeff (i - 1) else 0 := by
        rw [← mul_assoc]
        cases j with
        | zero => rw [coeff_mul_X_zero, coeff_zero]; simp
        | succ j' =>
            rw [coeff_mul_X, coeff_mul_C]
            cases i with
            | zero => rw [coeff_mul_X_zero]; simp
            | succ i' => rw [coeff_mul_X]; simp
      have hL3 : (((shiftBi x0 y0 (Fpoly.coeff 2) * X ^ 2).coeff j).coeff i) =
          if 2 ≤ j then ((shiftBi x0 y0 (Fpoly.coeff 2)).coeff (j - 2)).coeff i else 0 := by
        rw [mul_comm, coeff_X_pow_mul']; split_ifs <;> simp
      have hRHS_X : (X * Polynomial.expand (Polynomial F) 2 Po).coeff j =
          if j = 0 then 0 else (Polynomial.expand (Polynomial F) 2 Po).coeff (j - 1) := by
        cases j with | zero => rw [coeff_X_mul_zero]; rfl | succ j' => rw [coeff_X_mul]; simp
      rw [coeff_add, coeff_add, coeff_add, coeff_add, hL1, hL2, hL3, coeff_add, coeff_add,
        hRHS_X, coeff_expand_two_bi]
      -- Compute RHS coefficients explicitly for Pe and Po!
      have hPe_c : ∀ j0 i0, (Pe.coeff j0).coeff i0 =
          (if i0 % 2 = 0 ∧ 2 ≤ i0 then A0 (i0 / 2 - 1) j0 else 0) +
          (if i0 % 2 = 0 ∧ 1 ≤ j0 then A2 (i0 / 2) (j0 - 1) else 0) := by
        intro j0 i0; dsimp [Pe]
        simp only [coeff_add, coeff_C_mul, coeff_X_pow_mul']
        apply congrArg₂ (· + ·)
        · split_ifs with h1 h2
          · rw [coeff_mkEvenBi]
            have hdiv : (i0 - 2) / 2 = i0 / 2 - 1 := by omega
            rw [hdiv]
            by_cases ha : i0 / 2 - 1 ≤ W_F / 2
            · by_cases hb : j0 ≤ (Fpoly.coeff 0).natDegree / 2
              · rw [if_pos ⟨hb, by omega, ha⟩]
              · rw [if_neg (by tauto), hA0_b _ _ (by omega)]
            · rw [if_neg (by tauto), (hA_a _ _ (by omega)).1]
          · rw [coeff_mkEvenBi, if_neg (by omega)]
          · omega
          · rfl
        · cases j0 with
          | zero => rw [coeff_X_mul_zero, coeff_zero]; simp
          | succ j0' =>
              rw [coeff_X_mul]
              simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, le_add_iff_nonneg_left, zero_le, and_true,
                coeff_mkEvenBi]
              by_cases hi0 : i0 % 2 = 0
              · rw [if_pos hi0]
                by_cases ha : i0 / 2 ≤ W_F / 2
                · by_cases hb : j0' ≤ (Fpoly.coeff 2).natDegree / 2
                  · rw [if_pos ⟨hb, hi0, ha⟩]
                  · rw [if_neg (by tauto), hA2_b _ _ (by omega)]
                · rw [if_neg (by tauto), (hA_a _ _ (by omega)).2.2]
              · rw [if_neg hi0, if_neg (by tauto)]
      have hPo_c : ∀ j0 i0, (Po.coeff j0).coeff i0 =
          if i0 % 2 = 1 then A1 (i0 / 2) j0 else 0 := by
        intro j0 i0; dsimp [Po]; rw [coeff_C_mul]
        cases i0 with
        | zero => rw [coeff_X_mul_zero]; simp
        | succ i0' =>
            rw [coeff_X_mul]
            simp only [coeff_mkEvenBi]
            by_cases hi0 : (i0' + 1) % 2 = 1
            · rw [if_pos hi0]
              have hd : i0' / 2 = (i0' + 1) / 2 := by omega
              rw [hd]
              by_cases ha : (i0' + 1) / 2 ≤ W_F / 2
              · by_cases hb : j0 ≤ (Fpoly.coeff 1).natDegree / 2
                · rw [if_pos ⟨hb, by omega, ha⟩]
                · rw [if_neg (by tauto), hA1_b _ _ (by omega)]
              · rw [if_neg (by tauto), (hA_a _ _ (by omega)).2.1]
            · rw [if_neg hi0, if_neg (by omega)]
      -- Case split on parities of (i, j) (4 tiny cases, all C0/C1 pairs cancel in char 2!)
      rcases (show (i % 2 = 0 ∧ j % 2 = 0) ∨ (i % 2 = 1 ∧ j % 2 = 0) ∨
          (i % 2 = 0 ∧ j % 2 = 1) ∨ (i % 2 = 1 ∧ j % 2 = 1) by omega) with
        ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
      · -- i even, j even
        rw [if_pos hj]
        have hRHS_po : (if j = 0 then (0 : Polynomial F) else (Polynomial.expand (Polynomial F) 2 Po).coeff (j - 1)).coeff i = 0 := by
          cases j with
          | zero => simp
          | succ j' => simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]; rw [coeff_expand_two_bi, if_neg (by omega), coeff_zero]
        rw [hRHS_po, add_zero, hPe_c (j / 2) i]
        have hmid : (if 1 ≤ i ∧ 1 ≤ j then ((shiftBi x0 y0 (Fpoly.coeff 1)).coeff (j - 1)).coeff (i - 1) else 0) = 0 := by
          split_ifs with h1
          · rw [hshift_f1]; split_ifs <;> first | rfl | omega
          · rfl
        rw [hmid, add_zero]
        apply congrArg₂ (· + ·)
        · split_ifs with h1 h2
          · rw [hshift_f0, if_pos (by omega)]; congr 1 <;> omega
          · omega
          · omega
          · rfl
        · split_ifs with h1 h2
          · rw [hshift_f2, if_pos (by omega)]; congr 1 <;> omega
          · omega
          · omega
          · rfl
      · -- i odd, j even
        rw [if_pos hj]
        have hRHS_po : (if j = 0 then (0 : Polynomial F) else (Polynomial.expand (Polynomial F) 2 Po).coeff (j - 1)).coeff i = 0 := by
          cases j with
          | zero => simp
          | succ j' => simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]; rw [coeff_expand_two_bi, if_neg (by omega), coeff_zero]
        rw [hRHS_po, add_zero, hPe_c (j / 2) i]
        simp only [show ¬ i % 2 = 0 by omega, false_and, ↓reduceIte, add_zero]
        have h1 : (if 2 ≤ i then ((shiftBi x0 y0 (Fpoly.coeff 0)).coeff j).coeff (i - 2) else 0) = 0 := by
          split_ifs with h; · rw [hshift_f0]; split_ifs <;> first | rfl | omega
          · rfl
        rw [h1, zero_add]
        by_cases hj2 : 2 ≤ j
        · rw [if_pos ⟨by omega, by omega⟩, if_pos hj2, hshift_f1, hshift_f2]
          rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
          rw [show (i - 1) / 2 = i / 2 by omega, show (j - 1) / 2 = (j - 2) / 2 by omega]
          exact CharTwo.add_self_eq_zero _
        · have hj0 : j = 0 := by omega
          subst hj0; simp
      · -- i even, j odd
        rw [if_neg (by omega : ¬ j % 2 = 0), coeff_zero, zero_add]
        have hj1 : 1 ≤ j := by omega
        cases j with
        | zero => omega
        | succ j' =>
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_expand_two_bi,
              show j' % 2 = 0 by omega, hPo_c, show ¬ i % 2 = 1 by omega]
            have h3 : (if 2 ≤ j' + 1 then ((shiftBi x0 y0 (Fpoly.coeff 2)).coeff (j' + 1 - 2)).coeff i else 0) = 0 := by
              split_ifs with h; · rw [hshift_f2]; split_ifs <;> first | rfl | omega
              · rfl
            rw [h3, add_zero]
            by_cases hi2 : 2 ≤ i
            · rw [if_pos hi2, if_pos ⟨by omega, hj1⟩, hshift_f0, hshift_f1]
              rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
              rw [show (i - 2) / 2 = (i - 1) / 2 by omega, show (j' + 1) / 2 = j' / 2 by omega]
              exact CharTwo.add_self_eq_zero _
            · have hi0 : i = 0 := by omega
              subst hi0; simp
      · -- i odd, j odd
        rw [if_neg (by omega : ¬ j % 2 = 0), coeff_zero, zero_add]
        cases j with
        | zero => omega
        | succ j' =>
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, coeff_expand_two_bi,
              show j' % 2 = 0 by omega, hPo_c, hi]
            have h1 : (if 2 ≤ i then ((shiftBi x0 y0 (Fpoly.coeff 0)).coeff (j' + 1)).coeff (i - 2) else 0) = 0 := by
              split_ifs with h; · rw [hshift_f0]; split_ifs <;> first | rfl | omega
              · rfl
            have h3 : (if 2 ≤ j' + 1 then ((shiftBi x0 y0 (Fpoly.coeff 2)).coeff (j' + 1 - 2)).coeff i else 0) = 0 := by
              split_ifs with h; · rw [hshift_f2]; split_ifs <;> first | rfl | omega
              · rfl
            rw [h1, h3, zero_add, add_zero, if_pos ⟨by omega, by omega⟩, hshift_f1, if_pos (by omega)]
            rw [show (i - 1) / 2 = i / 2 by omega]
    have hPe_deg : 2 * Pe.natDegree ≤ max (Fpoly.coeff 0).natDegree ((Fpoly.coeff 2).natDegree + 2) := by
      have hle : Pe.natDegree ≤ max ((Fpoly.coeff 0).natDegree / 2) ((Fpoly.coeff 2).natDegree / 2 + 1) := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
        ext i; dsimp [Pe]; simp only [coeff_add, coeff_C_mul, coeff_X_pow_mul']
        have h1 : (if 2 ≤ i then ((mkEvenBi ((Fpoly.coeff 0).natDegree / 2) (W_F / 2) A0).coeff j).coeff (i - 2) else 0) = 0 := by
          split_ifs with h; · rw [coeff_mkEvenBi, if_neg (by omega)]
          · rfl
        have h2 : ((X * mkEvenBi ((Fpoly.coeff 2).natDegree / 2) (W_F / 2) A2).coeff j).coeff i = 0 := by
          cases j with | zero => rw [coeff_X_mul_zero, coeff_zero] | succ j' => rw [coeff_X_mul, coeff_mkEvenBi, if_neg (by omega)]
        rw [h1, h2, add_zero]
      omega
    have hPo_deg : 2 * Po.natDegree ≤ (Fpoly.coeff 1).natDegree := by
      have hle : Po.natDegree ≤ (Fpoly.coeff 1).natDegree / 2 := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro j hj
        ext i; dsimp [Po]; rw [coeff_C_mul]
        cases i with | zero => rw [coeff_X_mul_zero] | succ i' => rw [coeff_X_mul, coeff_mkEvenBi, if_neg (by omega)]
      omega
    have hPe_ord : weightedOrdGE 2 (2 * k + 2) Pe := by
      intro j; rw [X_pow_dvd_iff]; intro i hi
      dsimp [Pe]; simp only [coeff_add, coeff_C_mul, coeff_X_pow_mul']
      by_cases hi_ev : i % 2 = 0
      · by_cases hi2 : 2 ≤ i
        · cases j with
          | zero =>
              rw [coeff_X_mul_zero]
              simp only [hi2, ↓reduceIte, coeff_zero, add_zero, coeff_mkEvenBi]
              split_ifs with h
              · exact hA0_0_zero ((i - 2) / 2) (by omega)
              · rfl
          | succ j' =>
              rw [coeff_X_mul]
              simp only [hi2, ↓reduceIte, coeff_mkEvenBi]
              have h1 : (if j' + 1 ≤ (Fpoly.coeff 0).natDegree / 2 ∧ (i - 2) % 2 = 0 ∧ (i - 2) / 2 ≤ W_F / 2 then
                  A0 ((i - 2) / 2) (j' + 1) else 0) = A0 (i / 2 - 1) (j' + 1) := by
                rw [show (i - 2) / 2 = i / 2 - 1 by omega]
                split_ifs with h
                · rfl
                · symm; by_cases hb : j' + 1 ≤ (Fpoly.coeff 0).natDegree / 2
                  · exact (hA_a _ _ (by omega)).1
                  · exact hA0_b _ _ (by omega)
              have h2 : (if j' ≤ (Fpoly.coeff 2).natDegree / 2 ∧ i % 2 = 0 ∧ i / 2 ≤ W_F / 2 then
                  A2 (i / 2) j' else 0) = A2 (i / 2) j' := by
                split_ifs with h
                · rfl
                · symm; by_cases hb : j' ≤ (Fpoly.coeff 2).natDegree / 2
                  · exact (hA_a _ _ (by omega)).2.2
                  · exact hA2_b _ _ (by omega)
              rw [h1, h2, show i / 2 = (i / 2 - 1) + 1 by omega]
              exact hA0A2_zero (i / 2 - 1) j' (by omega)
        · have hi0 : i = 0 := by omega
          subst hi0
          rw [if_neg (by omega), zero_add]
          cases j with
          | zero => rw [coeff_X_mul_zero, coeff_zero]
          | succ j' =>
              rw [coeff_X_mul]
              simp only [coeff_mkEvenBi]
              split_ifs with h
              · exact hA2_0_zero j' (by omega)
              · rfl
      · have h1 : (if 2 ≤ i then ((mkEvenBi ((Fpoly.coeff 0).natDegree / 2) (W_F / 2) A0).coeff j).coeff (i - 2) else 0) = 0 := by
          split_ifs with h; · rw [coeff_mkEvenBi, if_neg (by omega)]
          · rfl
        have h2 : ((X * mkEvenBi ((Fpoly.coeff 2).natDegree / 2) (W_F / 2) A2).coeff j).coeff i = 0 := by
          cases j with | zero => rw [coeff_X_mul_zero, coeff_zero] | succ j' => rw [coeff_X_mul, coeff_mkEvenBi, if_neg (by omega)]
        rw [h1, h2, add_zero]
    have hPo_ord : weightedOrdGE 2 (2 * k + 1) Po := by
      intro j; rw [X_pow_dvd_iff]; intro i hi
      dsimp [Po]; rw [coeff_C_mul]
      cases i with
      | zero => rw [coeff_X_mul_zero]
      | succ i' =>
          rw [coeff_X_mul]
          simp only [coeff_mkEvenBi]
          split_ifs with h
          · exact hA1_zero (i' / 2) j (by omega)
          · rfl
    exact ⟨Pe, Po, hPe_eq, hPe_deg, hPo_deg, hPe_ord, hPo_ord,
      weightedOrdGE_sq_add_X_mul_sq Pe Po (2 * k + 2) (2 * k + 1) (4 * k + 4) hPe_ord hPo_ord (by omega) (by omega)⟩
  obtain ⟨Pe, Po, h1, h2, h3, h4, h5, h6⟩ := hstep4 A0 A1 A2 C0 C1
    hshift_f0 hshift_f1 hshift_f2 hA0_b hA1_b hA2_b hA_a hA0_0_zero hA2_0_zero hA0A2_zero hA1_zero
  exact ⟨hbm0, hbm1, hbm2, Pe, Po, h1, h2, h3, h4, h5, h6⟩

end KerDLocalDecomp

/-! ### Part 3: Global Degree, Leading-Coeff, Resultant, and Sum-of-Orders Bounds -/

section GlobalBounds

variable {F : Type*} [Field F]

/-- Weighted `(1, wY)` degree of a bivariate polynomial `f : BiPoly F`. -/
noncomputable def wdegBi (wY : ℕ) (f : BiPoly F) : ℕ :=
  f.support.sup fun j => (f.coeff j).natDegree + j * wY

lemma wdegBi_le_iff (wY W : ℕ) (f : BiPoly F) :
    wdegBi wY f ≤ W ↔ ∀ j i, ((f.coeff j).coeff i ≠ 0) → i + j * wY ≤ W := by
  unfold wdegBi; rw [Finset.sup_le_iff]
  constructor
  · intro h j i hnz
    have hj : j ∈ f.support := Polynomial.mem_support_iff.mpr (fun h0 => hnz (by simp [h0]))
    have hi : i ≤ (f.coeff j).natDegree := Polynomial.le_natDegree_of_ne_zero hnz
    have := h j hj; omega
  · intro h j hj
    have hne : f.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    have hnz : (f.coeff j).coeff (f.coeff j).natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
    exact h j _ hnz

lemma wdegBi_coeff_le {wY W : ℕ} {Fpoly : ContactPoly F} (hW : wdeg wY Fpoly ≤ W) (k : ℕ) :
    wdegBi wY (Fpoly.coeff k) ≤ W - k * (wY - 1) := by
  rw [wdegBi_le_iff]; intro j i hnz
  have hle := (wdeg_le_iff wY W Fpoly).mp hW k j i hnz
  omega

lemma natDegree_leadingCoeff_le_wdegBi {wY W df : ℕ} {f : BiPoly F}
    (hf : wdegBi wY f ≤ W) (hd : f.natDegree = df) :
    f.leadingCoeff.natDegree ≤ W - df * wY := by
  by_cases hf0 : f = 0
  · simp [hf0]
  · have hnz : (f.coeff df).coeff (f.coeff df).natDegree ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (by rw [← hd]; exact Polynomial.leadingCoeff_ne_zero.mpr hf0)
    have hle := (wdegBi_le_iff wY W f).mp hf df _ hnz
    rw [Polynomial.leadingCoeff, hd]; omega

/-- For any `f : BiPoly F` with `f.natDegree = df` and `biMultGE x0 y0 f m`,
`(X - C x0) ^ (m - df) ∣ f.leadingCoeff`! -/
theorem pow_dvd_leadingCoeff_of_biMultGE (x0 y0 : F) (f : BiPoly F) (df m : ℕ)
    (hd : f.natDegree = df) (hm : biMultGE x0 y0 f m) :
    (X - C x0) ^ (m - df) ∣ f.leadingCoeff := by
  have hcoeff : (shiftBi x0 y0 f).coeff df = f.leadingCoeff.comp (C x0 + X) := by
    unfold shiftBi
    have hmap_deg : (f.map (Polynomial.compRingHom (C x0 + X))).natDegree ≤ df :=
      Polynomial.natDegree_map_le.trans (le_of_eq hd)
    have hcomp_c : ∀ (p : BiPoly F) (n : ℕ), p.natDegree ≤ n →
        (p.comp (C (C y0) + X)).coeff n = p.coeff n := by
      intro p n hpn
      conv_lhs => rw [p.as_sum_range' (n + 1) (by omega)]
      rw [Polynomial.sum_comp, finset_sum_coeff]
      rw [Finset.sum_eq_single n]
      · rw [monomial_comp, coeff_C_mul, add_comm, add_pow, finset_sum_coeff, Finset.sum_eq_single n]
        · simp [coeff_X_pow, Nat.choose_self]
        · intro l hl hne
          have : X ^ l * (C (C y0) : BiPoly F) ^ (n - l) * (Nat.choose n l : BiPoly F) =
              C (C (y0 ^ (n - l) * (Nat.choose n l : F))) * X ^ l := by
            simp only [map_mul, map_pow, map_natCast]; ring
          rw [this, coeff_C_mul_X_pow, if_neg hne.symm]
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · intro k hk hne
        have hlt : k < n := by have := Finset.mem_range.mp hk; omega
        rw [monomial_comp, coeff_C_mul]
        have hdeg : ((C (C y0) + X : BiPoly F) ^ k).natDegree ≤ k := by
          refine Polynomial.natDegree_pow_le.trans ?_
          have : (C (C y0) + X : BiPoly F).natDegree ≤ 1 :=
            (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
          nlinarith only [this]
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := (C (C y0) + X : BiPoly F) ^ k) (by omega), mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [hcomp_c _ df hmap_deg, Polynomial.coeff_map, Polynomial.leadingCoeff, hd]; rfl
  have hdvd_X : X ^ (m - df) ∣ f.leadingCoeff.comp (C x0 + X) := by
    rw [← hcoeff, X_pow_dvd_iff]; intro i hi; exact hm i df (by omega)
  rcases hdvd_X with ⟨q, hq⟩
  refine ⟨q.comp (X - C x0), ?_⟩
  have hcomp := congrArg (fun p : Polynomial F => p.comp (X - C x0)) hq
  simp only [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
    Polynomial.mul_comp, Polynomial.pow_comp] at hcomp
  have h1 : C x0 + (X - C x0) = X := by ring
  rw [h1, Polynomial.comp_X] at hcomp
  exact hcomp

/-- **Univariate `X - C x0` divisibility from `X ^ m ∣ p.comp (C x0 + X)`:** -/
lemma X_sub_C_pow_dvd_of_comp_shift (x0 : F) (p : Polynomial F) (m : ℕ)
    (h : X ^ m ∣ p.comp (C x0 + X)) : (X - C x0) ^ m ∣ p := by
  rcases h with ⟨q, hq⟩
  refine ⟨q.comp (X - C x0), ?_⟩
  have hc := congrArg (fun r : Polynomial F => r.comp (X - C x0)) hq
  simp only [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
    Polynomial.mul_comp, Polynomial.pow_comp] at hc
  rw [show C x0 + (X - C x0) = X by ring, Polynomial.comp_X] at hc
  exact hc

/-- **Global `X`-degree bound for `Polynomial.resultant f g df dg` from `wdegBi`:**
`(Polynomial.resultant f g df dg).natDegree ≤ dg * W_f + df * W_g - df * dg * wY`! -/
theorem natDegree_resultant_le_wdegBi (wY W_f W_g df dg : ℕ) (f g : BiPoly F)
    (hWf : wdegBi wY f ≤ W_f) (hWg : wdegBi wY g ≤ W_g)
    (hdf : f.natDegree ≤ df) (hdg : g.natDegree ≤ dg) :
    (Polynomial.resultant f g df dg).natDegree ≤ dg * W_f + df * W_g - df * dg * wY := by
  classical
  rw [Polynomial.resultant, Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hunit : ((↑(Equiv.Perm.sign σ) : ℤ) : Polynomial F).natDegree = 0 := by
    rw [← Polynomial.C_eq_intCast]; exact Polynomial.natDegree_C _
  rw [hunit, zero_add]
  by_cases hzero : ∃ j : Fin (df + dg), Polynomial.sylvester f g df dg (σ j) j = 0
  · obtain ⟨j, hj⟩ := hzero
    rw [Finset.prod_eq_zero (f := fun i => Polynomial.sylvester f g df dg (σ i) i) (Finset.mem_univ j) hj,
      Polynomial.natDegree_zero]; exact Nat.zero_le _
  · push Not at hzero
    let jr : Fin df → ℕ := fun r' => (σ (Fin.castAdd dg r')).val - r'.val
    let ir : Fin dg → ℕ := fun r => (σ (Fin.natAdd df r)).val - r.val
    have hbounds :
      (∀ r' : Fin df, r'.val ≤ (σ (Fin.castAdd dg r')).val ∧
        (σ (Fin.castAdd dg r')).val ≤ r'.val + dg ∧
        Polynomial.sylvester f g df dg (σ (Fin.castAdd dg r')) (Fin.castAdd dg r') = g.coeff (jr r')) ∧
      (∀ r : Fin dg, r.val ≤ (σ (Fin.natAdd df r)).val ∧
        (σ (Fin.natAdd df r)).val ≤ r.val + df ∧
        Polynomial.sylvester f g df dg (σ (Fin.natAdd df r)) (Fin.natAdd df r) = f.coeff (ir r)) := by
      constructor
      · intro r'; have hne := hzero (Fin.castAdd dg r')
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc; · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
      · intro r; have hne := hzero (Fin.natAdd df r)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc] at hne ⊢
        split_ifs at hne ⊢ with hc; · exact ⟨hc.1, hc.2, rfl⟩
        · exact absurd rfl hne
    have hsum : (∑ r : Fin dg, ir r) + (∑ r' : Fin df, jr r') = df * dg := by
      have hperm : ∑ k : Fin (df + dg), (σ k).val = ∑ k : Fin (df + dg), k.val :=
        Equiv.sum_comp σ (fun k : Fin (df + dg) => k.val)
      rw [Fin.sum_univ_add, Fin.sum_univ_add] at hperm
      have hG : (∑ r' : Fin df, jr r') + (∑ r' : Fin df, r'.val) = ∑ r' : Fin df, (σ (Fin.castAdd dg r')).val := by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r' _
        have := (hbounds.1 r').1; dsimp [jr]; omega
      have hF : (∑ r : Fin dg, ir r) + (∑ r : Fin dg, r.val) = ∑ r : Fin dg, (σ (Fin.natAdd df r)).val := by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r _
        have := (hbounds.2 r).1; dsimp [ir]; omega
      have hadd : ∑ r : Fin dg, (Fin.natAdd df r).val = dg * df + ∑ r : Fin dg, r.val := by
        simp only [Fin.val_natAdd, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      have hcomm : dg * df = df * dg := mul_comm dg df
      simp only [Fin.val_castAdd] at hperm
      omega
    have hdeg_g : ∀ r' : Fin df, (g.coeff (jr r')).natDegree + jr r' * wY ≤ W_g := fun r' => by
      have hne : g.coeff (jr r') ≠ 0 := by rw [← (hbounds.1 r').2.2]; exact hzero (Fin.castAdd dg r')
      have hnz := Polynomial.leadingCoeff_ne_zero.mpr hne
      exact (wdegBi_le_iff wY W_g g).mp hWg (jr r') _ hnz
    have hdeg_f : ∀ r : Fin dg, (f.coeff (ir r)).natDegree + ir r * wY ≤ W_f := fun r => by
      have hne : f.coeff (ir r) ≠ 0 := by rw [← (hbounds.2 r).2.2]; exact hzero (Fin.natAdd df r)
      have hnz := Polynomial.leadingCoeff_ne_zero.mpr hne
      exact (wdegBi_le_iff wY W_f f).mp hWf (ir r) _ hnz
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    rw [Fin.sum_univ_add]
    have hs1 : (∑ r' : Fin df, (Polynomial.sylvester f g df dg (σ (Fin.castAdd dg r')) (Fin.castAdd dg r')).natDegree) +
        (∑ r' : Fin df, jr r') * wY ≤ df * W_g := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      calc ∑ r' : Fin df, ((Polynomial.sylvester f g df dg (σ (Fin.castAdd dg r')) (Fin.castAdd dg r')).natDegree + jr r' * wY)
          ≤ ∑ _ : Fin df, W_g := Finset.sum_le_sum fun r' _ => by rw [(hbounds.1 r').2.2]; exact hdeg_g r'
        _ = df * W_g := by simp
    have hs2 : (∑ r : Fin dg, (Polynomial.sylvester f g df dg (σ (Fin.natAdd df r)) (Fin.natAdd df r)).natDegree) +
        (∑ r : Fin dg, ir r) * wY ≤ dg * W_f := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      calc ∑ r : Fin dg, ((Polynomial.sylvester f g df dg (σ (Fin.natAdd df r)) (Fin.natAdd df r)).natDegree + ir r * wY)
          ≤ ∑ _ : Fin dg, W_f := Finset.sum_le_sum fun r _ => by rw [(hbounds.2 r).2.2]; exact hdeg_f r
        _ = dg * W_f := by simp
    have hsumW : (∑ r : Fin dg, ir r) * wY + (∑ r' : Fin df, jr r') * wY = df * dg * wY := by
      rw [← add_mul, hsum]
    omega

/-- **Univariate Sum-of-Orders Bound:**
For any nonzero `R : Polynomial F` and injective points `x : ι ↪ F`,
`(∀ i ∈ S, (X - C (x i)) ^ m i ∣ R) → ∑ i ∈ S, m i ≤ R.natDegree`! -/
theorem sum_ord_univariate_le {ι : Type*} [DecidableEq ι] (x : ι ↪ F) (S : Finset ι)
    (R : Polynomial F) (hR : R ≠ 0) (m : ι → ℕ)
    (hdvd : ∀ i ∈ S, (X - C (x i)) ^ m i ∣ R) :
    ∑ i ∈ S, m i ≤ R.natDegree := by
  have hprod : (∏ i ∈ S, (X - C (x i)) ^ m i) ∣ R := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      apply IsCoprime.pow
      have hne : x j - x i ≠ 0 := sub_ne_zero.mpr (fun h => hij (x.injective h.symm))
      refine ⟨C (x j - x i)⁻¹, -C (x j - x i)⁻¹, ?_⟩
      calc C (x j - x i)⁻¹ * (X - C (x i)) + -C (x j - x i)⁻¹ * (X - C (x j))
          = C (x j - x i)⁻¹ * C (x j - x i) := by rw [map_sub]; ring
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hne, map_one]
    · exact hdvd
  have hdeg : (∏ i ∈ S, (X - C (x i)) ^ m i).natDegree = ∑ i ∈ S, m i := by
    rw [Polynomial.natDegree_prod _ _ (fun i _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))]
    simp [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
  rw [← hdeg]
  exact Polynomial.natDegree_le_of_dvd hprod hR

/-- **Bivariate Evaluation `evalBi` Sum-of-Orders Bound:**
If `h : BiPoly F` has `wdegBi wY h ≤ W_h`, `P : Polynomial F` has `P.natDegree ≤ wY`, `h.eval P ≠ 0`,
and `∀ i ∈ Az, biMultGE (x i) (P.eval (x i)) h (m i)`, then `∑ i ∈ Az, m i ≤ W_h`! -/
theorem sum_biMultGE_eval_le {ι : Type*} [DecidableEq ι] (x : ι ↪ F) (Az : Finset ι)
    (wY W_h : ℕ) (h : BiPoly F) (P : Polynomial F) (m : ι → ℕ)
    (hP : P.natDegree ≤ wY) (hWh : wdegBi wY h ≤ W_h)
    (hne : h.eval P ≠ 0)
    (hm : ∀ i ∈ Az, biMultGE (x i) (P.eval (x i)) h (m i)) :
    ∑ i ∈ Az, m i ≤ W_h := by
  have hdvd : ∀ i ∈ Az, (X - C (x i)) ^ m i ∣ h.eval P := by
    intro i hi
    apply X_sub_C_pow_dvd_of_comp_shift (x i) (h.eval P) (m i)
    -- (h.eval P).comp (C (x i) + X) = (shiftBi (x i) (P.eval (x i)) h).eval (P.comp (C (x i) + X) - C (P.eval (x i)))!
    set Q : Polynomial F := P.comp (C (x i) + X) - C (P.eval (x i))
    have hXQ : X ∣ Q := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_C_zero,
        Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_X, add_zero, sub_self]
    have heval_eq : (h.eval P).comp (C (x i) + X) = (shiftBi (x i) (P.eval (x i)) h).eval Q := by
      unfold shiftBi
      rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      have hQadd : C (P.eval (x i)) + Q = P.comp (C (x i) + X) := by dsimp [Q]; ring
      rw [hQadd]
      exact (Polynomial.eval_map_apply (f := Polynomial.compRingHom (C (x i) + X)) (x := P) (p := h)).symm
    rw [heval_eq, Polynomial.eval_eq_sum_range]
    apply Finset.dvd_sum; intro j _
    have h1 : X ^ (m i - j) ∣ (shiftBi (x i) (P.eval (x i)) h).coeff j := by
      simpa only [one_mul] using (biMultGE_iff_weightedOrdGE_one (x i) (P.eval (x i)) h (m i)).mp (hm i hi) j
    have h2 : X ^ j ∣ Q ^ j := pow_dvd_pow_of_dvd hXQ j
    have h3 : X ^ ((m i - j) + j) ∣ (shiftBi (x i) (P.eval (x i)) h).coeff j * Q ^ j := by
      rw [pow_add]; exact mul_dvd_mul h1 h2
    exact (pow_dvd_pow X (by omega : m i ≤ (m i - j) + j)).trans h3
  have hdeg : (h.eval P).natDegree ≤ W_h := by
    rw [Polynomial.eval_eq_sum_range]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    by_cases hc : h.coeff j = 0
    · simp [hc]
    · refine Polynomial.natDegree_mul_le.trans ?_
      have hnz := Polynomial.leadingCoeff_ne_zero.mpr hc
      have hle := (wdegBi_le_iff wY W_h h).mp hWh j _ hnz
      have hpj : (P ^ j).natDegree ≤ j * wY := Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left j hP)
      omega
  exact (sum_ord_univariate_le x Az (h.eval P) hne m hdvd).trans hdeg

end GlobalBounds

end B6401KerD2
end ProximityPrize.SubmissionBinaryLower
