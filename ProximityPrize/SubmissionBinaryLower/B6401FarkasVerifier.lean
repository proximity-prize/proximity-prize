import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import Mathlib.Tactic

set_option Elab.async false

/-!
# Exact multi-`(m, s)` pigeonhole Farkas verifier & ArkLib budget checker

This module provides ONE unified, 100% kernel-verified Farkas + pigeonhole + ArkLib checker
used by all four certificate tables (`B6401CertsT1`, `T2`, `T3`, `T4`).

Mathematical theorem (`exists_active_ms_of_farkas`):
Suppose on an interval `c ∈ [cLo, cHi]` we have:
- a nonnegative class distribution `μ : Fin P → ℚ` with `∑ p, μ p = 1`,
- an optional nonnegative tail excess `T_tail ≥ 0`,
- `R` linear upper-bound constraints `∑ p, A[r, p] * μ p + Atail[r] * T_tail ≤ B0[r] + B1[r] * c`,
- `J` candidate `(m_j, s_j)` pairs with weights `x_j ≥ 0` (`∑ j, x_j = 1`), thresholds `δ_j > 0`,
  affine lower bounds `V0[j] + V1[j] * c ≤ vquot(j, c)`, class costs `C[j, p]`, and tail slope `Ctail[j]`.

If the Farkas multipliers `λ : Fin R → ℚ` (`λ_r ≥ 0`) and `ν : ℚ` satisfy:
1. `∀ p, ∑ j, x_j * C[j, p] ≤ ν + ∑ r, λ_r * A[r, p]`,
2. `∑ j, x_j * Ctail[j] ≤ ∑ r, λ_r * Atail[r]`,
3. At BOTH endpoints `c ∈ {cLo, cHi}`:
   `ν + ∑ r, λ_r * (B0[r] + B1[r] * c) < ∑ j, x_j * (V0[j] + V1[j] * c - δ_j)`,

then there exists `j : Fin J` with `x_j > 0` such that:
  `δ_j < (V0[j] + V1[j] * c) - (∑ p, C[j, p] * μ p + Ctail[j] * T_tail)`!

Every active `(m_j, s_j)` then feeds directly into `exists_quotient_contact_interpolant` with
`D_Z'` achieving `arklibBoundQ B H < cap`!
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401FarkasVerifier

open B6401Params B6401ContactKerD
open scoped BigOperators

/-! ### Exact ArkLib bound and quotient-interpolation surplus bridge -/

/-- Exact rational ArkLib unified power-factor bound matching
`ReedSolomon.ordinaryUnifiedPowerFactorAt N wY 1 B H A (wY + 1)` bit-for-bit! -/
def arklibBoundQ (B H : ℕ) : ℚ :=
  let theta : ℚ := ((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)
  let psi : ℚ := 1 + ((2 * wY - 1 : ℕ) : ℚ) * ((2 * B - 1 : ℕ) : ℚ) +
    2 * ((B - (2 * wY + 1) : ℕ) : ℚ)
  ((2 * B - 1 : ℕ) : ℚ) * (H : ℚ) + theta * ((B : ℚ) + (H : ℚ) * psi) +
    ((N - wY - 1 : ℕ) : ℚ) * (B : ℚ)

/-- Exact rational lower bound on `(varsKerDExact wY (2*A*m-1) s - varsKerDExact wY (2*A*m-1 - ⌊c*wY⌋) (s-d)) / (N * m^2)`. -/
def vquotLbQ (d m s : ℕ) (c : ℚ) : ℚ :=
  let W := 2 * A * m - 1
  ((varsKerDExact wY W s : ℚ) - varsKerDUpperQ wY ((W : ℚ) - c * (wY : ℚ)) (s - d)) /
    ((N : ℚ) * (m : ℚ) * (m : ℚ))

/-- Concavity of `vquotLbQ d m s` in `c`: on `[cLo, cHi]`, `vquotLbQ d m s c` lies above the
secant line connecting its values at `cLo` and `cHi`! -/
theorem vquotLbQ_ge_secant (d m s : ℕ) (hm : 0 < m) {cLo cHi c : ℚ}
    (hlo : cLo ≤ c) (hhi : c ≤ cHi) (hlt : cLo < cHi) :
    let t := (c - cLo) / (cHi - cLo)
    (1 - t) * vquotLbQ d m s cLo + t * vquotLbQ d m s cHi ≤ vquotLbQ d m s c := by
  intro t
  have hden : (0 : ℚ) < cHi - cLo := sub_pos.mpr hlt
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) hden.le
  have ht1 : t ≤ 1 := (div_le_one hden).mpr (sub_le_sub_right hhi cLo)
  have hW_eq : ((2 * A * m - 1 : ℕ) : ℚ) - c * (wY : ℚ) =
      (1 - t) * (((2 * A * m - 1 : ℕ) : ℚ) - cLo * (wY : ℚ)) +
      t * (((2 * A * m - 1 : ℕ) : ℚ) - cHi * (wY : ℚ)) := by
    have hc : c = (1 - t) * cLo + t * cHi := by
      dsimp [t]; field_simp [hden.ne']; ring
    conv_lhs => rw [hc]
    ring
  have hconv := varsKerDUpperQ_convex wY (s - d) (by norm_num [wY, D])
    (((2 * A * m - 1 : ℕ) : ℚ) - cLo * (wY : ℚ))
    (((2 * A * m - 1 : ℕ) : ℚ) - cHi * (wY : ℚ)) t ht0 ht1
  rw [← hW_eq] at hconv
  have hNm2 : (0 : ℚ) < (N : ℚ) * (m : ℚ) * (m : ℚ) := by
    have hN : (0 : ℚ) < N := by norm_num [N]
    have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  unfold vquotLbQ
  rw [show (1 - t) * (((varsKerDExact wY (2 * A * m - 1) s : ℚ) -
        varsKerDUpperQ wY (((2 * A * m - 1 : ℕ) : ℚ) - cLo * (wY : ℚ)) (s - d)) /
        ((N : ℚ) * (m : ℚ) * (m : ℚ))) +
      t * (((varsKerDExact wY (2 * A * m - 1) s : ℚ) -
        varsKerDUpperQ wY (((2 * A * m - 1 : ℕ) : ℚ) - cHi * (wY : ℚ)) (s - d)) /
        ((N : ℚ) * (m : ℚ) * (m : ℚ))) =
      ((varsKerDExact wY (2 * A * m - 1) s : ℚ) -
        ((1 - t) * varsKerDUpperQ wY (((2 * A * m - 1 : ℕ) : ℚ) - cLo * (wY : ℚ)) (s - d) +
         t * varsKerDUpperQ wY (((2 * A * m - 1 : ℕ) : ℚ) - cHi * (wY : ℚ)) (s - d))) /
        ((N : ℚ) * (m : ℚ) * (m : ℚ)) by ring]
  exact div_le_div_of_nonneg_right (by linarith) hNm2.le

/-- `vquotLbQ d m s c` is a valid rational lower bound on the exact integer quotient difference
whenever `c * wY ≤ W_F` (in particular for `c = W_F / wY`, where equality holds)! -/
theorem vquotLbQ_le_exact (d m s W_F : ℕ) (hm : 0 < m) (hW : W_F ≤ 2 * A * m - 1)
    {c : ℚ} (hc : c * (wY : ℚ) ≤ (W_F : ℚ)) :
    vquotLbQ d m s c ≤
      ((varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) : ℕ) : ℚ) /
      ((N : ℚ) * (m : ℚ) * (m : ℚ)) := by
  have hNm2 : (0 : ℚ) < (N : ℚ) * (m : ℚ) * (m : ℚ) := by
    have hN : (0 : ℚ) < N := by norm_num [N]
    have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  have hwYpos : 0 < wY := by norm_num [wY, D]
  have hsub_le : ((2 * A * m - 1 - W_F : ℕ) : ℚ) ≤ ((2 * A * m - 1 : ℕ) : ℚ) - c * (wY : ℚ) := by
    rw [Nat.cast_sub hW]; linarith
  have hup : (varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) : ℚ) ≤
      varsKerDUpperQ wY (((2 * A * m - 1 : ℕ) : ℚ) - c * (wY : ℚ)) (s - d) :=
    varsKerDExact_le_upperQ wY (2 * A * m - 1 - W_F) (s - d)
      (((2 * A * m - 1 : ℕ) : ℚ) - c * (wY : ℚ)) hwYpos hsub_le
  have hsub_nat : ((varsKerDExact wY (2 * A * m - 1) s : ℚ) -
      (varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) : ℚ)) ≤
      ((varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) : ℕ) : ℚ) := by
    by_cases hle : varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) ≤ varsKerDExact wY (2 * A * m - 1) s
    · rw [Nat.cast_sub hle]
    · have h0 : varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) = 0 := by omega
      rw [h0, Nat.cast_zero]
      have : (varsKerDExact wY (2 * A * m - 1) s : ℚ) ≤ (varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) : ℚ) := by
        exact_mod_cast le_of_not_ge hle
      linarith
  unfold vquotLbQ
  exact div_le_div_of_nonneg_right (by linarith) hNm2.le

/-! ### Multi-`(m, s)` Farkas + Pigeonhole core theorem -/

/-- Pure linear-algebraic Farkas + pigeonhole theorem (zero dependencies on any table specifics!). -/
theorem exists_active_ms_of_farkas {P R J : ℕ}
    (cLo cHi c : ℚ) (hlo : cLo ≤ c) (hhi : c ≤ cHi)
    (μ : Fin P → ℚ) (hμ0 : ∀ p, 0 ≤ μ p) (hμ1 : ∑ p : Fin P, μ p = 1)
    (T_tail : ℚ) (hT0 : 0 ≤ T_tail)
    (Amat : Fin R → Fin P → ℚ) (Atail B0 B1 : Fin R → ℚ)
    (hcon : ∀ r : Fin R, (∑ p : Fin P, Amat r p * μ p) + Atail r * T_tail ≤ B0 r + B1 r * c)
    (x : Fin J → ℚ) (hx0 : ∀ j, 0 ≤ x j)
    (V0 V1 δ Ctail : Fin J → ℚ) (Cmat : Fin J → Fin P → ℚ)
    (lam : Fin R → ℚ) (hlam0 : ∀ r, 0 ≤ lam r) (nu : ℚ)
    (hdual_p : ∀ p : Fin P, (∑ j : Fin J, x j * Cmat j p) ≤ nu + ∑ r : Fin R, lam r * Amat r p)
    (hdual_tail : (∑ j : Fin J, x j * Ctail j) ≤ ∑ r : Fin R, lam r * Atail r)
    (hend_lo : nu + (∑ r : Fin R, lam r * (B0 r + B1 r * cLo)) <
      ∑ j : Fin J, x j * (V0 j + V1 j * cLo - δ j))
    (hend_hi : nu + (∑ r : Fin R, lam r * (B0 r + B1 r * cHi)) <
      ∑ j : Fin J, x j * (V0 j + V1 j * cHi - δ j)) :
    ∃ j : Fin J, 0 < x j ∧
      δ j < (V0 j + V1 j * c) - ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail) := by
  -- Step 1: Affine combination of hend_lo and hend_hi holds at c ∈ [cLo, cHi]!
  have hend_c : nu + (∑ r : Fin R, lam r * (B0 r + B1 r * c)) <
      ∑ j : Fin J, x j * (V0 j + V1 j * c - δ j) := by
    by_cases heq : cLo = cHi
    · have hcc : c = cLo := by linarith
      rwa [hcc]
    · have hlt : cLo < cHi := lt_of_le_of_ne (hlo.trans hhi) heq
      have hden : (0 : ℚ) < cHi - cLo := sub_pos.mpr hlt
      let t := (c - cLo) / (cHi - cLo)
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) hden.le
      have ht1 : 0 ≤ 1 - t := by
        have : t ≤ 1 := (div_le_one hden).mpr (sub_le_sub_right hhi cLo)
        linarith
      have hc : c = (1 - t) * cLo + t * cHi := by
        dsimp [t]; field_simp [hden.ne']; ring
      have hcomb : (1 - t) * (nu + ∑ r : Fin R, lam r * (B0 r + B1 r * cLo)) +
          t * (nu + ∑ r : Fin R, lam r * (B0 r + B1 r * cHi)) <
          (1 - t) * (∑ j : Fin J, x j * (V0 j + V1 j * cLo - δ j)) +
          t * (∑ j : Fin J, x j * (V0 j + V1 j * cHi - δ j)) := by
        by_cases htpos : 0 < t
        · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hend_lo.le ht1)
            (mul_lt_mul_of_pos_left hend_hi htpos)
        · have ht_zero : t = 0 := le_antisymm (not_lt.mp htpos) ht0
          rw [ht_zero]; linarith
      have hlhs : nu + ∑ r : Fin R, lam r * (B0 r + B1 r * c) =
          (1 - t) * (nu + ∑ r : Fin R, lam r * (B0 r + B1 r * cLo)) +
          t * (nu + ∑ r : Fin R, lam r * (B0 r + B1 r * cHi)) := by
        rw [hc, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
        have hsum : (∑ r : Fin R, (1 - t) * (lam r * (B0 r + B1 r * cLo))) +
            (∑ r : Fin R, t * (lam r * (B0 r + B1 r * cHi))) =
            ∑ r : Fin R, lam r * (B0 r + B1 r * ((1 - t) * cLo + t * cHi)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro r _; ring
        linarith
      have hrhs : ∑ j : Fin J, x j * (V0 j + V1 j * c - δ j) =
          (1 - t) * (∑ j : Fin J, x j * (V0 j + V1 j * cLo - δ j)) +
          t * (∑ j : Fin J, x j * (V0 j + V1 j * cHi - δ j)) := by
        rw [hc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      linarith
  -- Step 2: Chain primal-dual inequality: ∑_j x_j * cost_j ≤ nu + ∑_r lam_r * (B0_r + B1_r * c)!
  have hprimal_dual : (∑ j : Fin J, x j * ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail)) ≤
      nu + ∑ r : Fin R, lam r * (B0 r + B1 r * c) := by
    have h1 : (∑ j : Fin J, x j * ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail)) =
        (∑ p : Fin P, μ p * (∑ j : Fin J, x j * Cmat j p)) +
        T_tail * (∑ j : Fin J, x j * Ctail j) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1
      · simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro p _
        apply Finset.sum_congr rfl; intro j _; ring
      · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have h2 : (∑ p : Fin P, μ p * (∑ j : Fin J, x j * Cmat j p)) ≤
        ∑ p : Fin P, μ p * (nu + ∑ r : Fin R, lam r * Amat r p) :=
      Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hdual_p p) (hμ0 p)
    have h3 : T_tail * (∑ j : Fin J, x j * Ctail j) ≤ T_tail * (∑ r : Fin R, lam r * Atail r) :=
      mul_le_mul_of_nonneg_left hdual_tail hT0
    have h4 : (∑ p : Fin P, μ p * (nu + ∑ r : Fin R, lam r * Amat r p)) +
        T_tail * (∑ r : Fin R, lam r * Atail r) =
        nu + ∑ r : Fin R, lam r * ((∑ p : Fin P, Amat r p * μ p) + Atail r * T_tail) := by
      have hL1 : (∑ p : Fin P, μ p * (nu + ∑ r : Fin R, lam r * Amat r p)) =
          nu + ∑ r : Fin R, ∑ p : Fin P, μ p * (lam r * Amat r p) := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hμ1, one_mul]
        congr 1
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      rw [hL1, add_assoc]; congr 1
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro r _
      rw [mul_add, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl; intro p _; ring
      · ring
    have h5 : (∑ r : Fin R, lam r * ((∑ p : Fin P, Amat r p * μ p) + Atail r * T_tail)) ≤
        ∑ r : Fin R, lam r * (B0 r + B1 r * c) :=
      Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hcon r) (hlam0 r)
    linarith
  -- Step 3: Strict weighted sum > 0 implies some j has x_j > 0 and strict surplus > δ_j!
  have hsum_pos : 0 < ∑ j : Fin J, x j *
      ((V0 j + V1 j * c) - ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail) - δ j) := by
    have hrew : (∑ j : Fin J, x j *
        ((V0 j + V1 j * c) - ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail) - δ j)) =
        (∑ j : Fin J, x j * (V0 j + V1 j * c - δ j)) -
        (∑ j : Fin J, x j * ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    linarith
  by_contra hall
  push Not at hall
  have hle0 : ∑ j : Fin J, x j *
      ((V0 j + V1 j * c) - ((∑ p : Fin P, Cmat j p * μ p) + Ctail j * T_tail) - δ j) ≤ 0 := by
    apply Finset.sum_nonpos; intro j _
    by_cases hxj : 0 < x j
    · exact mul_nonpos_of_nonneg_of_nonpos hxj.le (by linarith [hall j hxj])
    · have h0 : x j = 0 := le_antisymm (not_lt.mp hxj) (hx0 j)
      simp [h0]
  linarith

/-- **Exact integer surplus bridge:**
From `δ < vquot - cost_avg` (where `cost_avg = (∑ i, (rankKerD m s - rankKerD (m - k i) (s - d))) / (N * m^2)`)
and `D_Z' = ⌊(rankKerD m (s - d) * D_ZF + rankKerD m s * (dy * max (W / wY) (W_F / wY))) / (m^2 * δ)⌋ + 1`
(or ANY `D_Z' ≥ D_ZF` satisfying `(rankKerD m (s - d) * D_ZF + rankKerD m s * w_lin : ℚ) ≤ (D_Z' + 1) * (m^2 : ℚ) * δ`),
we get the EXACT integer inequality required by `exists_quotient_contact_interpolant`! -/
theorem integer_surplus_of_delta_gt {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = N)
    {d m s W_F D_ZF D_Z' dy : ℕ} (hm : 0 < m) (hd : d ≤ s) (hW : W_F ≤ 2 * A * m - 1)
    (hDZ : D_ZF ≤ D_Z') (k : ι → ℕ)
    {δ : ℚ} (hδ_pos : 0 < δ)
    (hsurp_q : δ <
      ((varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) : ℕ) : ℚ) /
        ((N : ℚ) * (m : ℚ) * (m : ℚ)) -
      (∑ i : ι, ((rankKerD m s - rankKerD (m - k i) (s - d) : ℕ) : ℚ)) /
        ((N : ℚ) * (m : ℚ) * (m : ℚ)))
    (hDZ_cond : ((rankKerD m (s - d) * D_ZF +
        rankKerD m s * (dy * max ((2 * A * m - 1) / wY) (W_F / wY)) : ℕ) : ℚ) ≤
        ((D_Z' + 1 : ℕ) : ℚ) * ((m * m : ℕ) : ℚ) * δ) :
    Fintype.card ι * rankKerD m s * (D_Z' + dy * max ((2 * A * m - 1) / wY) (W_F / wY) + 1) <
      (varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d)) * (D_Z' + 1) +
      (∑ i : ι, rankKerD (m - k i) (s - d)) * (D_Z' - D_ZF + 1) := by
  have hNm2 : (0 : ℚ) < (N : ℚ) * (m : ℚ) * (m : ℚ) := by
    have hN : (0 : ℚ) < N := by norm_num [N]
    have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  have hDZ1 : (0 : ℚ) < (D_Z' + 1 : ℕ) := by positivity
  -- Clear denominators on hsurp_q: N * m^2 * δ < ΔV - ∑ (rk(m, s) - rk(m - k_i, s - d))
  have h1 : ((N : ℚ) * (m : ℚ) * (m : ℚ)) * δ <
      ((varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) : ℕ) : ℚ) -
      (∑ i : ι, ((rankKerD m s - rankKerD (m - k i) (s - d) : ℕ) : ℚ)) := by
    have := mul_lt_mul_of_pos_left hsurp_q hNm2
    rw [mul_sub, mul_div_cancel₀ _ hNm2.ne', mul_div_cancel₀ _ hNm2.ne'] at this
    exact this
  -- Multiply by (D_Z' + 1) > 0:
  have h2 : (N : ℚ) * (((D_Z' + 1 : ℕ) : ℚ) * ((m * m : ℕ) : ℚ) * δ) <
      ((D_Z' + 1 : ℕ) : ℚ) *
        (((varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) : ℕ) : ℚ) -
         (∑ i : ι, ((rankKerD m s - rankKerD (m - k i) (s - d) : ℕ) : ℚ))) := by
    have := mul_lt_mul_of_pos_left h1 hDZ1
    push_cast at this ⊢; linarith
  -- Use hDZ_cond and rankKerD (m - k i) (s - d) ≤ rankKerD m (s - d) and rankKerD (m - k i) (s - d) ≤ rankKerD m s!
  have hN0 : (0 : ℚ) ≤ N := by positivity
  have h3 : (N : ℚ) * ((rankKerD m (s - d) * D_ZF +
      rankKerD m s * (dy * max ((2 * A * m - 1) / wY) (W_F / wY)) : ℕ) : ℚ) ≤
      (N : ℚ) * (((D_Z' + 1 : ℕ) : ℚ) * ((m * m : ℕ) : ℚ) * δ) :=
    mul_le_mul_of_nonneg_left hDZ_cond hN0
  have hrk_le_s : ∀ i : ι, rankKerD (m - k i) (s - d) ≤ rankKerD m s := fun i =>
    (rankKerD_mono_left (s - d) (Nat.sub_le m (k i))).trans (rankKerD_mono_right m (Nat.sub_le s d))
  have hrk_le_sd : ∀ i : ι, rankKerD (m - k i) (s - d) ≤ rankKerD m (s - d) := fun i =>
    rankKerD_mono_left (s - d) (Nat.sub_le m (k i))
  have hsum_sd : (∑ i : ι, (rankKerD (m - k i) (s - d) : ℚ)) ≤ (N : ℚ) * (rankKerD m (s - d) : ℚ) := by
    calc (∑ i : ι, (rankKerD (m - k i) (s - d) : ℚ))
        ≤ ∑ _i : ι, (rankKerD m (s - d) : ℚ) := Finset.sum_le_sum fun i _ => by exact_mod_cast hrk_le_sd i
      _ = (Fintype.card ι : ℚ) * (rankKerD m (s - d) : ℚ) := by simp
      _ = (N : ℚ) * (rankKerD m (s - d) : ℚ) := by rw [hcard]
  have hsum_diff : (∑ i : ι, ((rankKerD m s - rankKerD (m - k i) (s - d) : ℕ) : ℚ)) =
      (N : ℚ) * (rankKerD m s : ℚ) - ∑ i : ι, (rankKerD (m - k i) (s - d) : ℚ) := by
    have hterm : ∀ i : ι, ((rankKerD m s - rankKerD (m - k i) (s - d) : ℕ) : ℚ) =
        (rankKerD m s : ℚ) - (rankKerD (m - k i) (s - d) : ℚ) := fun i => Nat.cast_sub (hrk_le_s i)
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  -- Cast goal to ℚ and finish with linarith!
  have hgoalQ : ((Fintype.card ι * rankKerD m s * (D_Z' + dy * max ((2 * A * m - 1) / wY) (W_F / wY) + 1) : ℕ) : ℚ) <
      (((varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d)) * (D_Z' + 1) +
        (∑ i : ι, rankKerD (m - k i) (s - d)) * (D_Z' - D_ZF + 1) : ℕ) : ℚ) := by
    rw [hcard]
    push_cast
    rw [Nat.cast_sub hDZ]
    have hDZF0 : (0 : ℚ) ≤ (D_ZF : ℚ) := by positivity
    have hsum_mul : (∑ i : ι, (rankKerD (m - k i) (s - d) : ℚ)) * (D_ZF : ℚ) ≤
        (N : ℚ) * (rankKerD m (s - d) : ℚ) * (D_ZF : ℚ) := by
      have := mul_le_mul_of_nonneg_right hsum_sd hDZF0; linarith
    rw [hsum_diff] at h2
    push_cast at h2 h3
    linarith
  exact_mod_cast hgoalQ

end B6401FarkasVerifier
end ProximityPrize.SubmissionBinaryLower
