import ProximityPrize.SubmissionBinaryLower.Binary6402QuotBridgePart0
import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.Binary6402FarkasVerifier
import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid12
import ProximityPrize.SubmissionBinaryLower.Binary6402IntFarkas
import ProximityPrize.SubmissionBinaryLower.B6401T4Rows
import ProximityPrize.SubmissionBinaryLower.B6401T4Grid
import ProximityPrize.SubmissionBinaryLower.B6401CertsT4a
import ProximityPrize.SubmissionBinaryLower.B6401CertsT4b1
import ProximityPrize.SubmissionBinaryLower.B6401CertsT4b2
import ProximityPrize.SubmissionBinaryLower.B6401ResLineOrd
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 1600000

/-!
# Quotient-Surplus Bridge, `W < W_F` Handling, and Unified Cap Dispatch (`B6402QuotBridge`)

Connects ANY strict quotient-interpolation surplus
`(δNum / δDen) < vquotLbQ d m s (W_F / wY) - (∑ i, rankDiffQ d m s (k i)) / N`
(including the case `W = 2 * A * m - 1 < W_F` which occurs at `m = 8` for high `W_F`)
directly to:
1. `exists_quotient_contact_interpolant_wtd_any`: weighted denominator-free quotient interpolation
   for ALL `W_F : ℕ` (both `W_F ≤ W` and `W < W_F`).
2. `choose_DZ'_surplus`: optimal `D_Z'` achieving both the exact integer surplus inequality and
   `checkCapWitness_sound`'s `hDZ'_le` upper bound.
3. `card_le_of_quotient_surplus`: unified cap bound `(S.card : ℚ) ≤ w.c1Bkt * D_ZF + w.c0Bkt`
   for both `useP64 = false` (`d ∈ {1, 2}`) and `useP64 = true` (`d = 1, q₀ ∈ {1, 2}`).
4. `card_le_of_degZ_zero_surplus`: exact scalar root-count corollary (`dy = D_ZF = D_Z' = 0`)
   for `ScalarListBound`.
5. `t4a_hi1_no_p64` / `t4b1_hi1_no_p64` / `t4b2_hi1_no_p64`: kernel-`decide` proofs that no
   Table 4 bucket with `hiGNum = hiGDen` sets `useP64 = true`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402QuotBridge
set_option maxRecDepth 6000

open B6401Params hiding A
open B6402HybridP64 (A)
open Polynomial  B6401ContactKerD B6401QuotInterp B6402FarkasVerifier
open B6402HybridP64 B6402IntFarkas B6401T4Rows B6401T4Grid B6401ResLineOrd
open B6401CertsT4a B6401CertsT4b1 B6401CertsT4b2
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

/-- Unified weighted quotient contact interpolation for ALL `W_F : ℕ` (both `W_F ≤ W` and `W < W_F`)! -/
theorem exists_quotient_contact_interpolant_wtd_any {F ι : Type*} [Field F] [CharP F 2] [Fintype ι] [DecidableEq ι]
    (x : ι ↪ F) (y : ι → Polynomial F) {dy wY W_F d D_ZF m s W D_Z' : ℕ}
    (hwY : 2 ≤ wY) (hd : d ≤ s) (hDZ : D_ZF ≤ D_Z')
    (hD_ge : dy * (W / wY) ≤ D_Z')
    (hy : ∀ i, (y i).natDegree ≤ dy)
    (f_coord : KerDIdx wY W_F d → Polynomial F)
    (hf_wYZ : wYZ dy (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) ≤ D_ZF)
    (hFne : (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) ≠ 0)
    (hFdeg : (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1).natDegree = d)
    (hFwdeg : wdeg wY (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) = W_F)
    (k : ι → ℕ)
    (hk_exact : ∀ i,
      let Fi := ∑ e : KerDIdx wY W_F d, locC (f_coord e) * kerDLocalPoly (C (x i)) (y i) e.1
      k i ≤ m ∧ (k i < m → twOrdGE Fi (k i) ∧ ∃ p q, p + q = k i ∧ twCoeff Fi p q ≠ 0))
    (hsurplus :
      Fintype.card ι * rankKerD m s * (D_Z' + 1) +
        dy * (varsKerDExact wY W s - varsKerDExact wY (W - W_F) (s - d)) * (W / wY) <
      (varsKerDExact wY W s - varsKerDExact wY (W - W_F) (s - d)) * (D_Z' + 1) +
      (∑ i : ι, rankKerD (m - k i) (s - d)) * (D_Z' - D_ZF + 1)) :
    ∃ G : ContactPoly (Polynomial F),
      G ≠ 0 ∧ contactDeriv G = 0 ∧ G.natDegree ≤ s ∧ wdeg wY G ≤ W ∧
      wYZ dy G ≤ D_Z' ∧
      (∀ k' j' i', (((G.coeff k').coeff j').coeff i').natDegree ≤ D_Z') ∧
      (¬ ∃ Q' : ContactPoly (RatFunc F),
        G.map (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap (Polynomial F) (RatFunc F)))) =
        (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1).map
          (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap (Polynomial F) (RatFunc F)))) * Q') ∧
      (∀ (A : ℕ), W < 2 * A * m → ∀ (z : F) (P : Polynomial F),
        P.natDegree ≤ wY →
        ∀ (Az : Finset ι), A ≤ Az.card →
        (∀ i ∈ Az, P.eval (x i) = (y i).eval z) →
        evalContact (evalZContact (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) z) P = 0 →
        evalContact (evalZContact G z) P = 0) ∧
      (∃ (g_coord : KerDIdx wY W s → Polynomial F)
         (v_coord : ∀ i : ι, LocalBasisIdx (m - k i) (s - d) → Polynomial F),
        G = ∑ e : KerDIdx wY W s, cC (g_coord e) * kerDBasisPoly e.1 ∧
        ∀ i : ι, twOrdGE
          ((∑ e : KerDIdx wY W s, locC (g_coord e) * kerDLocalPoly (C (x i)) (y i) e.1) -
            (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (v_coord i b) * localBasisElem b.1)) m) := by
  by_cases hW : W_F ≤ W
  · exact exists_quotient_contact_interpolant_wtd x y (by omega) hd hW hDZ hD_ge hy f_coord hf_wYZ
      hFne hFdeg hFwdeg k hk_exact hsurplus
  · exact exists_quotient_contact_interpolant_wtd_lt x y hwY hd (by omega) hDZ hD_ge hy f_coord hf_wYZ
      hFne hFwdeg k hk_exact hsurplus

/-! ### Part 3: Optimal `D_Z'` Selection & Unified `card_le_of_quotient_surplus` -/

lemma wf_le_ceilDivNat {W_F cHiNum cHiDen : ℕ} (hcHiD : 0 < cHiDen)
    (hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ)) :
    W_F ≤ ceilDivNat (cHiNum * wY) cHiDen := by
  have hwYpos : (0 : ℚ) < (wY : ℚ) := by norm_num [wY]
  have hcHiDQ : (0 : ℚ) < (cHiDen : ℚ) := by exact_mod_cast hcHiD
  have hmulQ : (W_F : ℚ) * (cHiDen : ℚ) ≤ (cHiNum : ℚ) * (wY : ℚ) := by
    have := (div_le_div_iff₀ hwYpos hcHiDQ).mp hWF_hi
    linarith
  have hmulN : W_F * cHiDen ≤ cHiNum * wY := by exact_mod_cast hmulQ
  unfold ceilDivNat
  have h1 : W_F * cHiDen ≤ (cHiNum * wY + cHiDen - 1) := by omega
  have h2 : W_F ≤ (cHiNum * wY + cHiDen - 1) / cHiDen :=
    (Nat.le_div_iff_mul_le hcHiD).mpr h1
  exact h2

/-- Choose optimal `D_Z'` from a strict rational surplus `δNum / δDen < vquotLbQ - avg(rankDiffQ)`! -/
theorem choose_DZ'_surplus (d m s W_F D_ZF q₀ cHiNum cHiDen δNum δDen : ℕ)
    (hm : 0 < m) (hd : d ≤ s) (hcHiD : 0 < cHiDen) (hδNum : 0 < δNum) (hδDen : 0 < δDen)
    (hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (k : Idx → ℕ)
    (hsurp : (δNum : ℚ) / (δDen : ℚ) <
      vquotLbQ d m s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ d m s (k i)) / (N : ℚ)) :
    ∃ D_Z' : ℕ,
      D_ZF ≤ D_Z' ∧
      q₀ * ((2 * A * m - 1) / wY) ≤ D_Z' ∧
      ((D_Z' : ℚ) ≤ max ((D_ZF : ℚ) + (q₀ : ℚ) * (((2 * A * m - 1) / wY : ℕ) : ℚ))
        ((((rankKerD m (s - d) : ℚ) * (D_ZF : ℚ) +
            (q₀ : ℚ) * (((2 * A * m - 1) / wY : ℕ) : ℚ) *
              ((varsKerDExact wY (2 * A * m - 1) s -
                varsKerDExact wY ((2 * A * m - 1) - ceilDivNat (cHiNum * wY) cHiDen) (s - d) : ℕ) : ℚ) / (N : ℚ)) /
          (((m : ℚ) * (m : ℚ)) * ((δNum : ℚ) / (δDen : ℚ)))) + 1)) ∧
      (Fintype.card Idx * rankKerD m s * (D_Z' + 1) +
          q₀ * (varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d)) *
            ((2 * A * m - 1) / wY) <
        (varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d)) * (D_Z' + 1) +
        (∑ i : Idx, rankKerD (m - k i) (s - d)) * (D_Z' - D_ZF + 1)) := by
  let W := 2 * A * m - 1
  let ΔV := varsKerDExact wY W s - varsKerDExact wY (W - W_F) (s - d)
  let δ : ℚ := (δNum : ℚ) / (δDen : ℚ)
  have hδpos : (0 : ℚ) < δ := div_pos (by exact_mod_cast hδNum) (by exact_mod_cast hδDen)
  have hNpos : (0 : ℚ) < (N : ℚ) := by norm_num [N]
  have hmQpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hNm2pos : (0 : ℚ) < (N : ℚ) * (m : ℚ) * (m : ℚ) := by positivity
  let rhsQ : ℚ :=
    ((rankKerD m (s - d) : ℚ) * (D_ZF : ℚ) +
      (q₀ : ℚ) * ((W / wY : ℕ) : ℚ) * (ΔV : ℚ) / (N : ℚ)) /
      (((m : ℚ) * (m : ℚ)) * δ)
  have hrhsQ_nn : 0 ≤ rhsQ := by dsimp [rhsQ]; positivity
  let D_Z' : ℕ := max (D_ZF + q₀ * (W / wY)) (Nat.floor rhsQ + 1)
  have hDZ_le : D_ZF ≤ D_Z' := (Nat.le_add_right _ _).trans (le_max_left _ _)
  have hqW_le : q₀ * (W / wY) ≤ D_Z' := (Nat.le_add_left _ _).trans (le_max_left _ _)
  have hWF_cHi : W_F ≤ ceilDivNat (cHiNum * wY) cHiDen := wf_le_ceilDivNat hcHiD hWF_hi
  have hΔV_le : ΔV ≤ varsKerDExact wY W s -
      varsKerDExact wY (W - ceilDivNat (cHiNum * wY) cHiDen) (s - d) := by
    have hsub : W - ceilDivNat (cHiNum * wY) cHiDen ≤ W - W_F := Nat.sub_le_sub_left hWF_cHi W
    have hmono := varsKerDExact_mono_W wY (s - d) (by norm_num [wY]) hsub
    exact Nat.sub_le_sub_left hmono _
  have hDZ'_le : (D_Z' : ℚ) ≤ max ((D_ZF : ℚ) + (q₀ : ℚ) * ((W / wY : ℕ) : ℚ))
      ((((rankKerD m (s - d) : ℚ) * (D_ZF : ℚ) +
          (q₀ : ℚ) * ((W / wY : ℕ) : ℚ) *
            ((varsKerDExact wY W s -
              varsKerDExact wY (W - ceilDivNat (cHiNum * wY) cHiDen) (s - d) : ℕ) : ℚ) / (N : ℚ)) /
        (((m : ℚ) * (m : ℚ)) * δ)) + 1) := by
    dsimp only [D_Z']
    rw [Nat.cast_max]
    apply max_le_max
    · push_cast; exact le_rfl
    · have hfl : (Nat.floor rhsQ : ℚ) ≤ rhsQ := Nat.floor_le hrhsQ_nn
      have hΔQ : (ΔV : ℚ) ≤ ((varsKerDExact wY W s -
          varsKerDExact wY (W - ceilDivNat (cHiNum * wY) cHiDen) (s - d) : ℕ) : ℚ) := by
        exact_mod_cast hΔV_le
      have hrhs_le : rhsQ ≤
          ((rankKerD m (s - d) : ℚ) * (D_ZF : ℚ) +
            (q₀ : ℚ) * ((W / wY : ℕ) : ℚ) *
              ((varsKerDExact wY W s -
                varsKerDExact wY (W - ceilDivNat (cHiNum * wY) cHiDen) (s - d) : ℕ) : ℚ) / (N : ℚ)) /
          (((m : ℚ) * (m : ℚ)) * δ) := by
        dsimp only [rhsQ]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have h1 : (q₀ : ℚ) * ((W / wY : ℕ) : ℚ) * (ΔV : ℚ) / (N : ℚ) ≤
            (q₀ : ℚ) * ((W / wY : ℕ) : ℚ) *
              ((varsKerDExact wY W s -
                varsKerDExact wY (W - ceilDivNat (cHiNum * wY) cHiDen) (s - d) : ℕ) : ℚ) / (N : ℚ) := by
          apply div_le_div_of_nonneg_right _ hNpos.le
          exact mul_le_mul_of_nonneg_left hΔQ (by positivity)
        linarith
      push_cast; linarith
  -- Exact rational → integer surplus inequality!
  have hv_le := vquotLbQ_le_exact_any d m s W_F hm (c := (W_F : ℚ) / (wY : ℚ)) (by
    have hwQ : (wY : ℚ) ≠ 0 := by norm_num [wY]
    rw [div_mul_cancel₀ _ hwQ])
  have hrk_sum : (∑ i : Idx, rankDiffQ d m s (k i)) / (N : ℚ) =
      (∑ i : Idx, ((rankKerD m s - rankKerD (m - k i) (s - d) : ℕ) : ℚ)) / ((N : ℚ) * (m : ℚ) * (m : ℚ)) := by
    unfold rankDiffQ
    rw [← Finset.sum_div, div_div]; ring_nf
  have hsurp_ex : δ < (ΔV : ℚ) / ((N : ℚ) * (m : ℚ) * (m : ℚ)) -
      (∑ i : Idx, ((rankKerD m s - rankKerD (m - k i) (s - d) : ℕ) : ℚ)) / ((N : ℚ) * (m : ℚ) * (m : ℚ)) := by
    rw [← hrk_sum]; exact lt_of_lt_of_le hsurp (sub_le_sub_right hv_le _)
  have h1 : ((N : ℚ) * (m : ℚ) * (m : ℚ)) * δ <
      (ΔV : ℚ) - ∑ i : Idx, ((rankKerD m s - rankKerD (m - k i) (s - d) : ℕ) : ℚ) := by
    have := mul_lt_mul_of_pos_left hsurp_ex hNm2pos
    rw [mul_sub, mul_div_cancel₀ _ hNm2pos.ne', mul_div_cancel₀ _ hNm2pos.ne'] at this
    exact this
  have hDZ1_pos : (0 : ℚ) < ((D_Z' : ℚ) + 1) := by positivity
  have h2 : (N : ℚ) * (((D_Z' : ℚ) + 1) * ((m : ℚ) * (m : ℚ) * δ)) <
      ((D_Z' : ℚ) + 1) * ((ΔV : ℚ) - ∑ i : Idx, ((rankKerD m s - rankKerD (m - k i) (s - d) : ℕ) : ℚ)) := by
    have := mul_lt_mul_of_pos_left h1 hDZ1_pos
    linarith
  have hlt_DZ' : rhsQ < (D_Z' : ℚ) + 1 := by
    have h1' : rhsQ < (Nat.floor rhsQ : ℚ) + 1 := Nat.lt_floor_add_one rhsQ
    have h2' : ((Nat.floor rhsQ + 1 : ℕ) : ℚ) ≤ (D_Z' : ℚ) := by exact_mod_cast le_max_right _ _
    push_cast at h2'; linarith
  have hDZ_cond : (rankKerD m (s - d) : ℚ) * (D_ZF : ℚ) +
      (q₀ : ℚ) * ((W / wY : ℕ) : ℚ) * (ΔV : ℚ) / (N : ℚ) ≤
      ((D_Z' : ℚ) + 1) * ((m : ℚ) * (m : ℚ) * δ) := by
    have hden : (0 : ℚ) < (m : ℚ) * (m : ℚ) * δ := by positivity
    exact (div_le_iff₀ hden).mp hlt_DZ'.le
  have h3 : (N : ℚ) * (rankKerD m (s - d) : ℚ) * (D_ZF : ℚ) +
      (q₀ : ℚ) * (ΔV : ℚ) * ((W / wY : ℕ) : ℚ) ≤
      (N : ℚ) * (((D_Z' : ℚ) + 1) * ((m : ℚ) * (m : ℚ) * δ)) := by
    have := mul_le_mul_of_nonneg_left hDZ_cond hNpos.le
    rw [mul_add, show (N : ℚ) * ((q₀ : ℚ) * ((W / wY : ℕ) : ℚ) * (ΔV : ℚ) / (N : ℚ)) =
      (q₀ : ℚ) * (ΔV : ℚ) * ((W / wY : ℕ) : ℚ) by field_simp [hNpos.ne']] at this
    linarith
  have hcardIdx : Fintype.card Idx = N := BinaryIRSProfile.card_index
  have hrk_le_s : ∀ i : Idx, rankKerD (m - k i) (s - d) ≤ rankKerD m s := fun i =>
    (rankKerD_mono_left (s - d) (Nat.sub_le m (k i))).trans (rankKerD_mono_right m (Nat.sub_le s d))
  have hrk_le_sd : ∀ i : Idx, rankKerD (m - k i) (s - d) ≤ rankKerD m (s - d) := fun i =>
    rankKerD_mono_left (s - d) (Nat.sub_le m (k i))
  have hsum_sd : (∑ i : Idx, (rankKerD (m - k i) (s - d) : ℚ)) ≤ (N : ℚ) * (rankKerD m (s - d) : ℚ) := by
    calc _ ≤ ∑ _i : Idx, (rankKerD m (s - d) : ℚ) := Finset.sum_le_sum fun i _ => by exact_mod_cast hrk_le_sd i
      _ = (Fintype.card Idx : ℚ) * (rankKerD m (s - d) : ℚ) := by simp
      _ = (N : ℚ) * (rankKerD m (s - d) : ℚ) := by rw [hcardIdx]
  have hsum_diff : (∑ i : Idx, ((rankKerD m s - rankKerD (m - k i) (s - d) : ℕ) : ℚ)) =
      (N : ℚ) * (rankKerD m s : ℚ) - ∑ i : Idx, (rankKerD (m - k i) (s - d) : ℚ) := by
    have hterm : ∀ i : Idx, ((rankKerD m s - rankKerD (m - k i) (s - d) : ℕ) : ℚ) =
        (rankKerD m s : ℚ) - (rankKerD (m - k i) (s - d) : ℚ) := fun i => Nat.cast_sub (hrk_le_s i)
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardIdx]
  have hgoalQ : ((Fintype.card Idx * rankKerD m s * (D_Z' + 1) + q₀ * ΔV * (W / wY) : ℕ) : ℚ) <
      ((ΔV * (D_Z' + 1) + (∑ i : Idx, rankKerD (m - k i) (s - d)) * (D_Z' - D_ZF + 1) : ℕ) : ℚ) := by
    rw [hcardIdx]
    push_cast
    rw [Nat.cast_sub hDZ_le]
    have hDZF0 : (0 : ℚ) ≤ (D_ZF : ℚ) := Nat.cast_nonneg _
    have hmul_sd := mul_le_mul_of_nonneg_right hsum_sd hDZF0
    rw [hsum_diff] at h2
    linarith
  exact ⟨D_Z', hDZ_le, hqW_le, hDZ'_le, by exact_mod_cast hgoalQ⟩

lemma sum_v_cast {A : Type*} [CommRing A] {n1 n2 s : ℕ} (h : n1 = n2)
    (v : LocalBasisIdx n1 s → A) :
    ∃ v' : LocalBasisIdx n2 s → A,
      (∑ b : LocalBasisIdx n2 s, locC (v' b) * localBasisElem b.1) =
      ∑ b : LocalBasisIdx n1 s, locC (v b) * localBasisElem b.1 := by
  subst h; exact ⟨v, rfl⟩

/-- **Unified Master Quotient-Surplus → Cap Theorem (`card_le_of_quotient_surplus`):**
Given an irreducible `ker(D)` factor `F = ∑ e, cC (f_coord e) * kerDBasisPoly e.1` of `deg_R = d ∈ {1, 2}`,
`wdeg wY F = W_F`, `wYZ q₀ F ≤ D_ZF`, exact local orders `k : Idx → ℕ`, a strict rational surplus
`(δNum / δDen) < vquotLbQ d m s (W_F / wY) - (∑ i, rankDiffQ d m s (k i)) / N`, and a kernel-checked
`CapWitness` `w` (plus `d = 1` & `hG_hi` only when `w.useP64 = true`), concludes:
`(S.card : ℚ) ≤ (w.c1Bkt : ℚ) * (D_ZF : ℚ) + (w.c0Bkt : ℚ)`! -/
theorem gapAt6402 (u₀ u₁ : Idx → Fld) (q₀ W_F m s hiGNum hiGDen : ℕ)
    (hhiGDen : 0 < hiGDen)
    (Φ : Polynomial (Polynomial (Polynomial Fld)))
    (hWΦ : P64Caps.Weighted.weightedSupportDegree Φ wY ≤
      (2 * A * m - 1) + s * (W_F - (wY - 1)))
    (hWF_ge : wY - 1 ≤ W_F)
    (k : Idx → ℕ)
    (hord : ∀ i : Idx, (2 * (m : ℤ)) + (s : ℤ) * (2 * (k i : ℤ) - 1) ≤
      (P64LineOrder.lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ))
    (Az : Finset Idx)
    (hG_hi : (hiGDen : ℤ) * ((W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ∑ i ∈ Az, (2 * (k i : ℤ) - 1)) ≤ (hiGNum * N : ℤ)) :
    (P64Caps.Weighted.weightedSupportDegree Φ wY : ℤ) -
      (∑ i ∈ Az, (P64LineOrder.lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
      (2 * (m : ℤ)) * ((Az.card : ℤ) - (A : ℤ)) ≤
      ((s * hiGNum * N) / hiGDen : ℕ) := by
  have hWΦZ : (P64Caps.Weighted.weightedSupportDegree Φ wY : ℤ) ≤
      2 * (A : ℤ) * (m : ℤ) + (s : ℤ) * ((W_F : ℤ) - ((wY - 1 : ℕ) : ℤ)) := by
    have h1 : (P64Caps.Weighted.weightedSupportDegree Φ wY : ℤ) ≤
        ((2 * A * m - 1 : ℕ) : ℤ) + (s : ℤ) * ((W_F - (wY - 1) : ℕ) : ℤ) := by
      exact_mod_cast hWΦ
    have h2 : ((2 * A * m - 1 : ℕ) : ℤ) ≤ 2 * (A : ℤ) * (m : ℤ) := by
      have : 2 * A * m - 1 ≤ 2 * A * m := Nat.sub_le _ _
      exact_mod_cast this
    rw [Nat.cast_sub hWF_ge] at h1
    nlinarith
  have hsum_ord : (2 * (m : ℤ)) * (Az.card : ℤ) + (s : ℤ) * (∑ i ∈ Az, (2 * (k i : ℤ) - 1)) ≤
      ∑ i ∈ Az, (P64LineOrder.lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ) := by
    have h := Finset.sum_le_sum fun i (_ : i ∈ Az) => hord i
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h
    linarith
  set Gz : ℤ := (W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) - ∑ i ∈ Az, (2 * (k i : ℤ) - 1)
  have hlhs_le : (P64Caps.Weighted.weightedSupportDegree Φ wY : ℤ) -
      (∑ i ∈ Az, (P64LineOrder.lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
      (2 * (m : ℤ)) * ((Az.card : ℤ) - (A : ℤ)) ≤ (s : ℤ) * Gz := by
    dsimp [Gz]; linarith
  refine hlhs_le.trans ?_
  by_cases hGz : Gz ≤ 0
  · have h1 : (s : ℤ) * Gz ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg s) hGz
    exact h1.trans (Nat.cast_nonneg _)
  · push Not at hGz
    lift Gz to ℕ using le_of_lt hGz with g hg
    have hmulZ : (hiGDen : ℤ) * ((s * g : ℕ) : ℤ) ≤ ((s * hiGNum * N : ℕ) : ℤ) := by
      push_cast
      have := mul_le_mul_of_nonneg_left hG_hi (Nat.cast_nonneg s)
      nlinarith
    have hmulN : hiGDen * (s * g) ≤ s * hiGNum * N := by exact_mod_cast hmulZ
    have hdiv : s * g ≤ (s * hiGNum * N) / hiGDen :=
      (Nat.le_div_iff_mul_le hhiGDen).mpr (by rw [mul_comm]; exact hmulN)
    exact_mod_cast hdiv


theorem card_le_of_quotient_surplus
    (u₀ u₁ : Idx → Fld) {d m s W_F D_ZF q₀ cHiNum cHiDen δNum δDen hiGNum hiGDen : ℕ}
    (w : CapWitness)
    (hchk : checkCapWitness d m s cHiNum cHiDen δNum δDen hiGNum hiGDen q₀ w = true)
    (hq₀ : q₀ = 1 ∨ q₀ = 2)
    (hd1 : 1 ≤ d) (hds : d ≤ s) (hm : 0 < m)
    (hcHiD : 0 < cHiDen) (hδNum : 0 < δNum) (hδDen : 0 < δDen) (hhiGD : 0 < hiGDen)
    (hWF_lo : d * (wY - 1) ≤ W_F)
    (hWF_hi : (W_F : ℚ) / (wY : ℚ) ≤ (cHiNum : ℚ) / (cHiDen : ℚ))
    (f_coord : KerDIdx wY W_F d → Polynomial Fld)
    (hirr : Irreducible (liftCRat (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1)))
    (hFdeg : (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1).natDegree = d)
    (hFwdeg : wdeg wY (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) = W_F)
    (hf_wYZ : wYZ q₀ (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) ≤ D_ZF)
    (k : Idx → ℕ)
    (hk_exact : ∀ i : Idx,
      let Fi := ∑ e : KerDIdx wY W_F d, locC (f_coord e) * kerDLocalPoly (C (BinaryIRSProfile.domain i)) (linePow u₀ u₁ q₀ i) e.1
      twOrdGE Fi (k i) ∧ (k i < m → ∃ p q, p + q = k i ∧ twCoeff Fi p q ≠ 0))
    (hsurp : (δNum : ℚ) / (δDen : ℚ) <
      vquotLbQ d m s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ d m s (k i)) / (N : ℚ))
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hFvan : ∀ z ∈ S, evalContact (evalZContact (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) z) (P z) = 0)
    (hcard : ∀ z ∈ S, A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6402 u₀ u₁ (Az z))
    (hp64_extra : w.useP64 = true → d = 1 ∧
      ∀ z ∈ S, (hiGDen : ℤ) * ((W_F : ℤ) - ((wY - 1 : ℕ) : ℤ) -
        ∑ i ∈ Az z, (2 * (k i : ℤ) - 1)) ≤ (hiGNum * N : ℤ)) :
    (S.card : ℚ) ≤ (w.c1Bkt : ℚ) * (D_ZF : ℚ) + (w.c0Bkt : ℚ) := by
  let Fpoly : ContactPoly (Polynomial Fld) := ∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1
  have hFne : Fpoly ≠ 0 := by
    intro h0; exact hirr.ne_zero (by change liftCRat Fpoly = 0; rw [h0, map_zero])
  -- Cap k at m for interpolation (preserving exactness at k_cap < m and rankDiffQ!)
  let k_cap : Idx → ℕ := fun i => min (k i) m
  have hrk_eq : ∀ i, rankDiffQ d m s (k_cap i) = rankDiffQ d m s (k i) := by
    intro i; unfold rankDiffQ k_cap
    have : m - min (k i) m = m - k i := by omega
    rw [this]
  have hsurp_cap : (δNum : ℚ) / (δDen : ℚ) <
      vquotLbQ d m s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ d m s (k_cap i)) / (N : ℚ) := by
    simpa only [hrk_eq] using hsurp
  obtain ⟨D_Z', hDZ_le, hqW_le, hDZ'_le, hsurp_int⟩ :=
    choose_DZ'_surplus d m s W_F D_ZF q₀ cHiNum cHiDen δNum δDen hm hds hcHiD hδNum hδDen hWF_hi k_cap hsurp_cap
  have hy_deg : ∀ i : Idx, (linePow u₀ u₁ q₀ i).natDegree ≤ q₀ := by
    intro i; unfold linePow
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact natDegree_mul_le.trans (by simp)
  have hk_cap_ex : ∀ i : Idx,
      let Fi := ∑ e : KerDIdx wY W_F d, locC (f_coord e) * kerDLocalPoly (C (BinaryIRSProfile.domain i)) (linePow u₀ u₁ q₀ i) e.1
      k_cap i ≤ m ∧ (k_cap i < m → twOrdGE Fi (k_cap i) ∧ ∃ p q, p + q = k_cap i ∧ twCoeff Fi p q ≠ 0) := by
    intro i; dsimp only [k_cap]
    refine ⟨Nat.min_le_right _ _, fun hlt => ?_⟩
    have hkm : k i < m := by omega
    have heq : min (k i) m = k i := Nat.min_eq_left hkm.le
    rw [heq]; exact ⟨(hk_exact i).1, (hk_exact i).2 hkm⟩
  obtain ⟨G, hGne, _, hGdeg, hGwdeg, _, hGZ, hndvd, hGvan, g_coord, v_coord, hG_eq, hlocal⟩ :=
    exists_quotient_contact_interpolant_wtd_any BinaryIRSProfile.domain (linePow u₀ u₁ q₀)
      (by norm_num [wY]) hds hDZ_le hqW_le hy_deg f_coord hf_wYZ hFne hFdeg hFwdeg k_cap hk_cap_ex hsurp_int
  let Φ : Polynomial (Polynomial (Polynomial Fld)) := Polynomial.resultant Fpoly G d s
  have hΦne : Φ ≠ 0 := resultant_ne_zero_of_not_dvd Fpoly G d s hirr hFdeg hd1 hGdeg hGne hndvd
  have hWF_cHi : W_F ≤ ceilDivNat (cHiNum * wY) cHiDen := wf_le_ceilDivNat hcHiD hWF_hi
  have hWΦ_WF : P64Caps.Weighted.weightedSupportDegree Φ wY ≤
      d * (2 * A * m - 1) + s * (W_F - d * (wY - 1)) :=
    weightedSupportDegree_resultant_le Fpoly G wY W_F (2 * A * m - 1) d s (le_of_eq hFwdeg) hGwdeg hWF_lo
  have hWΦ : P64Caps.Weighted.weightedSupportDegree Φ wY ≤
      d * (2 * A * m - 1) + s * (ceilDivNat (cHiNum * wY) cHiDen - d * (wY - 1)) :=
    hWΦ_WF.trans (Nat.add_le_add_left (Nat.mul_le_mul_left s (Nat.sub_le_sub_right hWF_cHi _)) _)
  have hB : Φ.natDegree ≤
      (d * (2 * A * m - 1) + s * (ceilDivNat (cHiNum * wY) cHiDen - d * (wY - 1))) / wY :=
    (natDegree_le_weightedSupportDegree_div Φ wY (by norm_num [wY])).trans (Nat.div_le_div_right hWΦ)
  have hH : ∀ j a, ((Φ.coeff j).coeff a).natDegree ≤ d * D_Z' + s * D_ZF :=
    degZ_resultant_le Fpoly G d s D_ZF D_Z' (natDegree_Z_le_of_wYZ hf_wYZ) hGZ
  have hcurve : ∀ z ∈ S, triEval Φ z (P z) = 0 := by
    intro z hz
    have hGz : evalContact (evalZContact G z) (P z) = 0 := by
      refine hGvan A (by norm_num [A]; omega) z (P z) (hP z hz) (Az z) (hcard z hz) (fun i hi => ?_) (hFvan z hz)
      rw [(hmatch z hz i).mp hi]
      simp [linePow]; ring
    exact triEval_resultant_eq_zero Fpoly G d s (le_of_eq hFdeg) hGdeg (by omega) z (P z) (hFvan z hz) hGz
  refine checkCapWitness_sound u₀ u₁ d m s cHiNum cHiDen δNum δDen hiGNum hiGDen q₀ D_ZF D_Z' w
    hchk hq₀ hDZ'_le Φ hΦne hWΦ hB hH S P Az hP hcurve hcard hmatch hbad ?_
  intro huse z hz
  obtain ⟨hd_eq, hG_hi⟩ := hp64_extra huse
  subst hd_eq
  have hf1_ne : Fpoly.coeff 1 ≠ 0 := by
    rw [← hFdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hFne
  have hWΦ_1 : P64Caps.Weighted.weightedSupportDegree Φ wY ≤ (2 * A * m - 1) + s * (W_F - (wY - 1)) := by
    simpa only [one_mul] using hWΦ_WF
  have hord_k : ∀ i : Idx, (2 * (m : ℤ)) + (s : ℤ) * (2 * (k i : ℤ) - 1) ≤
      (P64LineOrder.lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ) := by
    intro i
    have hΦne' : Polynomial.resultant Fpoly (∑ e : KerDIdx wY (2 * A * m - 1) s, cC (g_coord e) * kerDBasisPoly e.1) 1 s ≠ 0 := by
      rwa [← hG_eq]
    have hsub_eq : m - k_cap i = m - k i := by dsimp [k_cap]; omega
    obtain ⟨v_i, hv_sum⟩ := sum_v_cast hsub_eq (v_coord i)
    have hloc_k := hlocal i
    rw [← hv_sum] at hloc_k
    have hord_i := lineOrd_resultant_deg1_ge (by norm_num [wY]) hds (BinaryIRSProfile.domain i)
      (linePow u₀ u₁ q₀ i) f_coord g_coord v_i hf1_ne (hk_exact i).1 hloc_k hΦne'
    dsimp only [Φ]; rw [hG_eq]; exact hord_i
  exact gapAt6402 u₀ u₁ q₀ W_F m s hiGNum hiGDen hhiGD Φ hWΦ_1 (by simpa using hWF_lo) k hord_k (Az z) (hG_hi z hz)

/-! ### Part 4: Free Scalar Root-Count Corollary (`card_le_of_degZ_zero_surplus`) -/

/-- Exact scalar (`deg_Z = 0, dy = 0`) root-count bound from any positive rational surplus! -/
theorem card_le_of_degZ_zero_surplus
    (u : Idx → Fld) {d m s W_F : ℕ}
    (hd1 : 1 ≤ d) (hds : d ≤ s) (hm : 0 < m) (hWF_lo : d * (wY - 1) ≤ W_F)
    (f_coord : KerDIdx wY W_F d → Fld)
    (hirr : Irreducible (liftCRat (∑ e : KerDIdx wY W_F d, cC (Polynomial.C (f_coord e)) * kerDBasisPoly e.1)))
    (hFdeg : (∑ e : KerDIdx wY W_F d, cC (Polynomial.C (f_coord e)) * kerDBasisPoly e.1).natDegree = d)
    (hFwdeg : wdeg wY (∑ e : KerDIdx wY W_F d, cC (Polynomial.C (f_coord e)) * kerDBasisPoly e.1) = W_F)
    (k : Idx → ℕ)
    (hk_exact : ∀ i : Idx,
      let Fi := ∑ e : KerDIdx wY W_F d, locC (Polynomial.C (f_coord e)) * kerDLocalPoly (C (BinaryIRSProfile.domain i)) (C (u i)) e.1
      twOrdGE Fi (k i) ∧ (k i < m → ∃ p q, p + q = k i ∧ twCoeff Fi p q ≠ 0))
    (hsurp : (0 : ℚ) <
      vquotLbQ d m s ((W_F : ℚ) / (wY : ℚ)) - (∑ i : Idx, rankDiffQ d m s (k i)) / (N : ℚ))
    (T : Finset (Polynomial Fld))
    (hT : ∀ P ∈ T, P.natDegree ≤ wY ∧
      A ≤ (Finset.univ.filter fun i : Idx => P.eval (BinaryIRSProfile.domain i) = u i).card ∧
      evalContact (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) P = 0) :
    T.card ≤ (d * (2 * A * m - 1) + s * (W_F - d * (wY - 1))) / wY := by
  let fcZ : KerDIdx wY W_F d → Polynomial Fld := fun e => Polynomial.C (f_coord e)
  let Fpoly : ContactPoly (Polynomial Fld) := ∑ e : KerDIdx wY W_F d, cC (fcZ e) * kerDBasisPoly e.1
  have hFne : Fpoly ≠ 0 := fun h0 => hirr.ne_zero (by change liftCRat Fpoly = 0; rw [h0, map_zero])
  have hf_wYZ : wYZ 0 Fpoly ≤ 0 := by
    apply wYZ_sum_kerDBasisPoly_le (by norm_num [wY]) fcZ
    intro e _; simp [fcZ]
  let k_cap : Idx → ℕ := fun i => min (k i) m
  have hrk_eq : ∀ i, rankDiffQ d m s (k_cap i) = rankDiffQ d m s (k i) := by
    intro i; unfold rankDiffQ k_cap
    have : m - min (k i) m = m - k i := by omega
    rw [this]
  have hsurp_int :
      Fintype.card Idx * rankKerD m s * (0 + 1) +
        0 * (varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d)) *
          ((2 * A * m - 1) / wY) <
      (varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d)) * (0 + 1) +
      (∑ i : Idx, rankKerD (m - k_cap i) (s - d)) * (0 - 0 + 1) := by
    have hv_le := vquotLbQ_le_exact_any d m s W_F hm (c := (W_F : ℚ) / (wY : ℚ)) (by
      have hwQ : (wY : ℚ) ≠ 0 := by norm_num [wY]
      rw [div_mul_cancel₀ _ hwQ])
    have hrk_sum : (∑ i : Idx, rankDiffQ d m s (k_cap i)) / (N : ℚ) =
        (∑ i : Idx, ((rankKerD m s - rankKerD (m - k_cap i) (s - d) : ℕ) : ℚ)) / ((N : ℚ) * (m : ℚ) * (m : ℚ)) := by
      unfold rankDiffQ; rw [← Finset.sum_div, div_div]; ring_nf
    have hNm2pos : (0 : ℚ) < (N : ℚ) * (m : ℚ) * (m : ℚ) := by
      have hN : (0 : ℚ) < (N : ℚ) := by norm_num [N]
      have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
      positivity
    have hsurp' : (0 : ℚ) <
        ((varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) : ℕ) : ℚ) /
          ((N : ℚ) * (m : ℚ) * (m : ℚ)) -
        (∑ i : Idx, ((rankKerD m s - rankKerD (m - k_cap i) (s - d) : ℕ) : ℚ)) /
          ((N : ℚ) * (m : ℚ) * (m : ℚ)) := by
      rw [← hrk_sum]; simp_rw [hrk_eq]; exact lt_of_lt_of_le hsurp (sub_le_sub_right hv_le _)
    have hmul := mul_lt_mul_of_pos_left hsurp' hNm2pos
    rw [mul_zero, mul_sub, mul_div_cancel₀ _ hNm2pos.ne', mul_div_cancel₀ _ hNm2pos.ne'] at hmul
    have hcardIdx : Fintype.card Idx = N := BinaryIRSProfile.card_index
    have hrk_le_s : ∀ i : Idx, rankKerD (m - k_cap i) (s - d) ≤ rankKerD m s := fun i =>
      (rankKerD_mono_left (s - d) (Nat.sub_le m (k_cap i))).trans (rankKerD_mono_right m (Nat.sub_le s d))
    have hsum_diff : (∑ i : Idx, ((rankKerD m s - rankKerD (m - k_cap i) (s - d) : ℕ) : ℚ)) =
        (N : ℚ) * (rankKerD m s : ℚ) - ∑ i : Idx, (rankKerD (m - k_cap i) (s - d) : ℚ) := by
      have hterm : ∀ i : Idx, ((rankKerD m s - rankKerD (m - k_cap i) (s - d) : ℕ) : ℚ) =
          (rankKerD m s : ℚ) - (rankKerD (m - k_cap i) (s - d) : ℚ) := fun i => Nat.cast_sub (hrk_le_s i)
      simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardIdx]
    rw [hsum_diff] at hmul
    have hgoalQ : ((Fintype.card Idx * rankKerD m s : ℕ) : ℚ) <
        ((varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) +
          ∑ i : Idx, rankKerD (m - k_cap i) (s - d) : ℕ) : ℚ) := by
      rw [hcardIdx]; push_cast; linarith
    have hnat : Fintype.card Idx * rankKerD m s <
        (varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d)) +
        ∑ i : Idx, rankKerD (m - k_cap i) (s - d) := by exact_mod_cast hgoalQ
    omega
  have hk_cap_ex : ∀ i : Idx,
      let Fi := ∑ e : KerDIdx wY W_F d, locC (fcZ e) * kerDLocalPoly (C (BinaryIRSProfile.domain i)) (C (u i)) e.1
      k_cap i ≤ m ∧ (k_cap i < m → twOrdGE Fi (k_cap i) ∧ ∃ p q, p + q = k_cap i ∧ twCoeff Fi p q ≠ 0) := by
    intro i; dsimp only [k_cap]
    refine ⟨Nat.min_le_right _ _, fun hlt => ?_⟩
    have hkm : k i < m := by omega
    have heq : min (k i) m = k i := Nat.min_eq_left hkm.le
    rw [heq]; exact ⟨(hk_exact i).1, (hk_exact i).2 hkm⟩
  obtain ⟨G, hGne, _, hGdeg, hGwdeg, _, hGZ, hndvd, hGvan, _⟩ :=
    exists_quotient_contact_interpolant_wtd_any BinaryIRSProfile.domain (fun i => Polynomial.C (u i))
      (by norm_num [wY]) hds le_rfl (by simp) (fun i => by simp) fcZ hf_wYZ hFne hFdeg hFwdeg k_cap hk_cap_ex hsurp_int
  have hF0_eq : evalZContact Fpoly 0 = ∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1 := by
    dsimp only [Fpoly, fcZ]; unfold evalZContact; simp only [Polynomial.map_sum, Polynomial.map_mul]
    apply Finset.sum_congr rfl; intro e _
    change evalZContact (cC (Polynomial.C (f_coord e))) 0 * evalZContact (kerDBasisPoly e.1) 0 = _
    rw [evalZContact_cC, evalZContact_kerDBasisPoly, Polynomial.eval_C]
  refine card_common_roots_le_of_resultant Fpoly G wY W_F (2 * A * m - 1) d s (by norm_num [wY])
    hirr hFdeg hd1 hGdeg hGne (le_of_eq hFwdeg) hGwdeg hWF_lo (natDegree_Z_le_of_wYZ hf_wYZ) hGZ hndvd T ?_
  intro P hP
  have ⟨hPdeg, hPcard, hPvan⟩ := hT P hP
  have hPF0 : evalContact (evalZContact Fpoly 0) P = 0 := by rw [hF0_eq]; exact hPvan
  refine ⟨hPF0, hGvan A (by norm_num [A]; omega) 0 P hPdeg
    (Finset.univ.filter fun i : Idx => P.eval (BinaryIRSProfile.domain i) = u i) hPcard ?_ hPF0⟩
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simpa [Polynomial.eval_C] using hi



end B6402QuotBridge
end ProximityPrize.SubmissionBinaryLower
