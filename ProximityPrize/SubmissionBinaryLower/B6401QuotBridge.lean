import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401QuotInterp
import ProximityPrize.SubmissionBinaryLower.B6401FarkasVerifier
import ProximityPrize.SubmissionBinaryLower.B6401HybridP64
import ProximityPrize.SubmissionBinaryLower.B6401IntFarkas
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
# Quotient-Surplus Bridge, `W < W_F` Handling, and Unified Cap Dispatch (`B6401QuotBridge`)

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
namespace B6401QuotBridge

open Polynomial B6401Params B6401ContactKerD B6401QuotInterp B6401FarkasVerifier
open B6401HybridP64 B6401IntFarkas B6401T4Rows B6401T4Grid B6401ResLineOrd
open B6401CertsT4a B6401CertsT4b1 B6401CertsT4b2
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped BigOperators

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

/-! ### Part 1: Exact `W < W_F` Dimension Bounds (`varsKerDExact_zero_W`, `vquotLbQ_le_exact_any`) -/

/-- For `wY ≥ 2`, the space `K_0(s)` contains only constants (`(0, 0, 0, 0)`), so `varsKerDExact wY 0 s = 1`. -/
theorem varsKerDExact_zero_W (wY s : ℕ) (hwY : 2 ≤ wY) : varsKerDExact wY 0 s = 1 := by
  unfold varsKerDExact
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro r hr hne
      have hr1 : r = 1 := by have := Finset.mem_range.mp hr; omega
      subst hr1; simp only [zero_mul, one_mul, zero_add]
      split_ifs with h1 h2
      · omega
      · rfl
      · rfl
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro k hk hne
    apply Finset.sum_eq_zero; intro r _
    have hpos : 0 < k * (wY - 1) + r * wY := by
      have : 0 < k * (wY - 1) := Nat.mul_pos (Nat.pos_of_ne_zero hne) (by omega)
      omega
    dsimp only
    split_ifs with h1 h2
    · omega
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos s)) h

/-- `varsKerDUpperQ wY W_q s ≥ 1` for EVERY `W_q : ℚ` (even negative `W_q`!), because the
`(k = 0, r = 0)` summand is `≥ 1` and every other summand is `≥ 0`. -/
theorem one_le_varsKerDUpperQ (wY : ℕ) (W_q : ℚ) (s : ℕ) (hwY : 0 < wY) :
    (1 : ℚ) ≤ varsKerDUpperQ wY W_q s := by
  have hwQ : (0 : ℚ) < (wY : ℚ) := by exact_mod_cast hwY
  have hterm_nn : ∀ k r : ℕ, (0 : ℚ) ≤
      if k + r ≤ s then
        let u := W_q - ((k * (wY - 1) + r * wY : ℕ) : ℚ)
        let u1 := max 0 (u + (wY : ℚ))
        let u0 := max 0 u
        u1 * u1 / (8 * (wY : ℚ)) + u0 / (2 * (wY : ℚ)) + 1
      else 0 := by
    intro k r
    split_ifs
    · have h1 : (0 : ℚ) ≤ max 0 (W_q - ((k * (wY - 1) + r * wY : ℕ) : ℚ) + (wY : ℚ)) := le_max_left _ _
      have h0 : (0 : ℚ) ≤ max 0 (W_q - ((k * (wY - 1) + r * wY : ℕ) : ℚ)) := le_max_left _ _
      positivity
    · exact le_rfl
  unfold varsKerDUpperQ
  have h0_mem : (0 : ℕ) ∈ Finset.range (s + 1) := Finset.mem_range.mpr (Nat.succ_pos s)
  have hr0_mem : (0 : ℕ) ∈ Finset.range 2 := Finset.mem_range.mpr (by omega)
  have h0_ge : (1 : ℚ) ≤ ∑ r ∈ Finset.range 2,
      if 0 + r ≤ s then
        let u := W_q - ((0 * (wY - 1) + r * wY : ℕ) : ℚ)
        let u1 := max 0 (u + (wY : ℚ))
        let u0 := max 0 u
        u1 * u1 / (8 * (wY : ℚ)) + u0 / (2 * (wY : ℚ)) + 1
      else 0 := by
    calc (1 : ℚ)
        ≤ (if 0 + 0 ≤ s then
            let u := W_q - ((0 * (wY - 1) + 0 * wY : ℕ) : ℚ)
            let u1 := max 0 (u + (wY : ℚ))
            let u0 := max 0 u
            u1 * u1 / (8 * (wY : ℚ)) + u0 / (2 * (wY : ℚ)) + 1
          else 0) := by
          simp only [Nat.add_zero, Nat.zero_le, ↓reduceIte]
          have h1 : (0 : ℚ) ≤ max 0 (W_q - ((0 * (wY - 1) + 0 * wY : ℕ) : ℚ) + (wY : ℚ)) := le_max_left _ _
          have h0 : (0 : ℚ) ≤ max 0 (W_q - ((0 * (wY - 1) + 0 * wY : ℕ) : ℚ)) := le_max_left _ _
          have hsq : (0 : ℚ) ≤ max 0 (W_q - ((0 * (wY - 1) + 0 * wY : ℕ) : ℚ) + (wY : ℚ)) *
              max 0 (W_q - ((0 * (wY - 1) + 0 * wY : ℕ) : ℚ) + (wY : ℚ)) / (8 * (wY : ℚ)) := by positivity
          have hlin : (0 : ℚ) ≤ max 0 (W_q - ((0 * (wY - 1) + 0 * wY : ℕ) : ℚ)) / (2 * (wY : ℚ)) := by positivity
          linarith
      _ ≤ _ := Finset.single_le_sum (fun r _ => hterm_nn 0 r) hr0_mem
  exact h0_ge.trans (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun r _ => hterm_nn k r) h0_mem)

/-- Monotonicity of `varsKerDExact` in `W`. -/
theorem varsKerDExact_mono_W (wY s : ℕ) (hwY : 0 < wY) {W1 W2 : ℕ} (h : W1 ≤ W2) :
    varsKerDExact wY W1 s ≤ varsKerDExact wY W2 s := by
  rw [← card_kerDIdxFinset wY W1 s hwY, ← card_kerDIdxFinset wY W2 s hwY]
  apply Finset.card_le_card
  intro ⟨k, r, b, a⟩ he
  have hm := (mem_kerDIdxFinset_iff wY W1 s hwY k r b a).mp he
  exact (mem_kerDIdxFinset_iff wY W2 s hwY k r b a).mpr ⟨hm.1, hm.2.1, hm.2.2.trans h⟩

/-- Unconditional `vquotLbQ_le_exact_any` — removes the `W_F ≤ 2 * A * m - 1` restriction! -/
theorem vquotLbQ_le_exact_any (d m s W_F : ℕ) (hm : 0 < m)
    {c : ℚ} (hc : c * (wY : ℚ) ≤ (W_F : ℚ)) :
    vquotLbQ d m s c ≤
      ((varsKerDExact wY (2 * A * m - 1) s - varsKerDExact wY (2 * A * m - 1 - W_F) (s - d) : ℕ) : ℚ) /
        ((N : ℚ) * (m : ℚ) * (m : ℚ)) := by
  by_cases hW : W_F ≤ 2 * A * m - 1
  · exact vquotLbQ_le_exact d m s W_F hm hW hc
  · have hsub0 : 2 * A * m - 1 - W_F = 0 := by omega
    rw [hsub0, varsKerDExact_zero_W wY (s - d) (by norm_num [wY])]
    have hNm2 : (0 : ℚ) < (N : ℚ) * (m : ℚ) * (m : ℚ) := by
      have hN : (0 : ℚ) < (N : ℚ) := by norm_num [N]
      have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
      positivity
    have h1_le : (1 : ℚ) ≤ varsKerDUpperQ wY (((2 * A * m - 1 : ℕ) : ℚ) - c * (wY : ℚ)) (s - d) :=
      one_le_varsKerDUpperQ wY _ (s - d) (by norm_num [wY])
    have hv_ge1 : 1 ≤ varsKerDExact wY (2 * A * m - 1) s := by
      have := varsKerDExact_mono_W wY s (by norm_num [wY]) (Nat.zero_le (2 * A * m - 1))
      rwa [varsKerDExact_zero_W wY s (by norm_num [wY])] at this
    unfold vquotLbQ
    apply div_le_div_of_nonneg_right _ hNm2.le
    rw [Nat.cast_sub hv_ge1, Nat.cast_one]
    linarith

/-- Since `(0, 0, 0, 0) ∈ kerDIdxFinset wY W s` contributes `0` to `yWeightSum` and every other
basis element has `2 * b + r ≤ W / wY`, we get `yWeightSum wY W s ≤ (varsKerDExact wY W s - 1) * (W / wY)`! -/
theorem yWeightSum_le_pred_mul (wY W s : ℕ) (hwY : 0 < wY) :
    yWeightSum wY W s ≤ (varsKerDExact wY W s - 1) * (W / wY) := by
  unfold yWeightSum
  have h0_mem : (0, 0, 0, 0) ∈ kerDIdxFinset wY W s :=
    (mem_kerDIdxFinset_iff wY W s hwY 0 0 0 0).mpr ⟨by omega, by omega, by simp⟩
  rw [← Finset.add_sum_erase _ _ h0_mem]
  simp only [Nat.mul_zero, Nat.add_zero, zero_add]
  calc ∑ e ∈ (kerDIdxFinset wY W s).erase (0, 0, 0, 0), (2 * e.2.2.1 + e.2.1)
      ≤ ∑ _e ∈ (kerDIdxFinset wY W s).erase (0, 0, 0, 0), (W / wY) := by
        apply Finset.sum_le_sum; intro ⟨k, r, b, a⟩ he
        have hm := (mem_kerDIdxFinset_iff wY W s hwY k r b a).mp (Finset.mem_of_mem_erase he)
        have hmul : (2 * b + r) * wY ≤ W := by nlinarith [hm.2.2]
        exact (Nat.le_div_iff_mul_le hwY).mpr hmul
    _ = ((kerDIdxFinset wY W s).erase (0, 0, 0, 0)).card * (W / wY) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (varsKerDExact wY W s - 1) * (W / wY) := by
        rw [Finset.card_erase_of_mem h0_mem, card_kerDIdxFinset wY W s hwY]

/-! ### Part 2: `W < W_F` Weighted Quotient Interpolation & Unified `exists_quotient_contact_interpolant_wtd_any` -/

/-- Weighted denominator-free 4-variable quotient interpolation in the `W < W_F` regime:
since `wdeg wY G ≤ W < W_F = wdeg wY F`, `F ∤ G` is automatic from `wdeg_mul` with NO quotient
complement `I0` needed (using all `varsKerDExact wY W s` variables)! -/
theorem exists_quotient_contact_interpolant_wtd_lt {F ι : Type*} [Field F] [CharP F 2] [Fintype ι] [DecidableEq ι]
    (x : ι ↪ F) (y : ι → Polynomial F) {dy wY W_F d D_ZF m s W D_Z' : ℕ}
    (hwY : 2 ≤ wY) (hd : d ≤ s) (hW : W < W_F) (hDZ : D_ZF ≤ D_Z')
    (hD_ge : dy * (W / wY) ≤ D_Z')
    (hy : ∀ i, (y i).natDegree ≤ dy)
    (f_coord : KerDIdx wY W_F d → Polynomial F)
    (hf_wYZ : wYZ dy (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) ≤ D_ZF)
    (hFne : (∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1) ≠ 0)
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
  classical
  have hwY1 : 1 ≤ wY := by omega
  have hwYpos : 0 < wY := by omega
  let Fpoly : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W_F d, cC (f_coord e) * kerDBasisPoly e.1
  let alg : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F)
  let liftC : ContactPoly (Polynomial F) →+* ContactPoly (RatFunc F) :=
    Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom alg))
  let cap (e : KerDIdx wY W s) : ℕ := D_Z' + 1 - dy * (2 * e.1.2.2.1 + e.1.2.1)
  have hbr_le : ∀ e : KerDIdx wY W s, dy * (2 * e.1.2.2.1 + e.1.2.1) ≤ dy * (W / wY) := by
    intro ⟨⟨k', r, b, a⟩, he⟩
    have hmem := (mem_kerDIdxFinset_iff wY W s hwYpos k' r b a).mp he
    have h1 : (2 * b + r) * wY ≤ W := by nlinarith [hmem.2.2]
    exact Nat.mul_le_mul_left dy ((Nat.le_div_iff_mul_le hwYpos).mpr h1)
  let I_G := Σ e : KerDIdx wY W s, Fin (cap e)
  let I_V := (Σ i : ι, LocalBasisIdx (m - k i) (s - d)) × Fin (D_Z' - D_ZF + 1)
  let I_all := I_G ⊕ I_V
  let J_all := ι × LocalBasisIdx m s × Fin (D_Z' + 1)
  let gPoly (u : I_all → F) (e : KerDIdx wY W s) : Polynomial F :=
    ∑ t : Fin (cap e), Polynomial.C (u (Sum.inl ⟨e, t⟩)) * (Polynomial.X : Polynomial F) ^ t.val
  let vPoly (u : I_all → F) (i : ι) (b : LocalBasisIdx (m - k i) (s - d)) : Polynomial F :=
    ∑ t : Fin (D_Z' - D_ZF + 1), Polynomial.C (u (Sum.inr (⟨i, b⟩, t))) * (Polynomial.X : Polynomial F) ^ t.val
  let L : (I_all → F) →ₗ[F] (J_all → F) :=
    { toFun := fun u j =>
        let (i, idx, t) := j
        ((∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) -
         (∑ b : LocalBasisIdx (m - k i) (s - d), vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx)).coeff t.val
      map_add' := by
        intro u1 u2; funext ⟨i, idx, t⟩
        have hg : ∀ e, gPoly (u1 + u2) e = gPoly u1 e + gPoly u2 e := fun e => by
          dsimp [gPoly]; simp [add_mul, Finset.sum_add_distrib]
        have hv : ∀ b, vPoly (u1 + u2) i b = vPoly u1 i b + vPoly u2 i b := fun b => by
          dsimp [vPoly]; simp [add_mul, Finset.sum_add_distrib]
        simp only [hg, hv, add_mul, Finset.sum_add_distrib, coeff_sub, coeff_add, Pi.add_apply]; ring
      map_smul' := by
        intro a u; funext ⟨i, idx, t⟩
        have hg : ∀ e, gPoly (a • u) e = C a * gPoly u e := fun e => by
          dsimp [gPoly]; simp [Finset.mul_sum, mul_assoc]
        have hv : ∀ b, vPoly (a • u) i b = C a * vPoly u i b := fun b => by
          dsimp [vPoly]; simp [Finset.mul_sum, mul_assoc]
        simp only [hg, hv, mul_assoc, ← Finset.mul_sum, ← mul_sub, coeff_C_mul, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply] }
  have hcard : Fintype.card J_all < Fintype.card I_all := by
    have hsub0 : W - W_F = 0 := by omega
    rw [hsub0, varsKerDExact_zero_W wY (s - d) hwY] at hsurplus
    have hv_ge1 : 1 ≤ varsKerDExact wY W s := by
      have := varsKerDExact_mono_W wY s hwYpos (Nat.zero_le W)
      rwa [varsKerDExact_zero_W wY s hwY] at this
    have hIG_eq : Fintype.card I_G + dy * yWeightSum wY W s = varsKerDExact wY W s * (D_Z' + 1) := by
      have h1 : Fintype.card I_G = ∑ e : KerDIdx wY W s, (D_Z' + 1 - dy * (2 * e.1.2.2.1 + e.1.2.1)) := by
        simp only [I_G, Fintype.card_sigma, Fintype.card_fin, cap]
      have h2 : dy * yWeightSum wY W s = ∑ e : KerDIdx wY W s, dy * (2 * e.1.2.2.1 + e.1.2.1) := by
        unfold yWeightSum; rw [Finset.mul_sum]
        symm
        exact Finset.sum_attach (kerDIdxFinset wY W s) (fun e => dy * (2 * e.2.2.1 + e.2.1))
      rw [h1, h2, ← Finset.sum_add_distrib]
      have hterm : ∀ e : KerDIdx wY W s,
          (D_Z' + 1 - dy * (2 * e.1.2.2.1 + e.1.2.1)) + dy * (2 * e.1.2.2.1 + e.1.2.1) = D_Z' + 1 := by
        intro e; have := (hbr_le e).trans hD_ge; omega
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, smul_eq_mul, card_kerDIdx wY W s hwYpos]
    have hyw_le : dy * yWeightSum wY W s ≤ dy * (varsKerDExact wY W s - 1) * (W / wY) := by
      have := Nat.mul_le_mul_left dy (yWeightSum_le_pred_mul wY W s hwYpos)
      calc dy * yWeightSum wY W s ≤ dy * ((varsKerDExact wY W s - 1) * (W / wY)) := this
        _ = dy * (varsKerDExact wY W s - 1) * (W / wY) := by ring
    have hIG_ge : (varsKerDExact wY W s - 1) * (D_Z' + 1) ≤
        Fintype.card I_G + dy * (varsKerDExact wY W s - 1) * (W / wY) := by
      have h1 : (varsKerDExact wY W s - 1) * (D_Z' + 1) ≤ varsKerDExact wY W s * (D_Z' + 1) :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      omega
    simp only [I_all, I_V, J_all, Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma,
      Fintype.card_fin, card_localBasisIdx]
    have hJ : Fintype.card ι * (rankKerD m s * (D_Z' + 1)) = Fintype.card ι * rankKerD m s * (D_Z' + 1) := by ring
    omega
  obtain ⟨u, hu_ne, hLu⟩ := exists_ne_zero_ker_linearMap L hcard
  let G : ContactPoly (Polynomial F) := ∑ e : KerDIdx wY W s, cC (gPoly u e) * kerDBasisPoly e.1
  have hg_wtd : ∀ e : KerDIdx wY W s, (gPoly u e).natDegree + dy * (2 * e.1.2.2.1 + e.1.2.1) ≤ D_Z' := by
    intro e
    have hle := (hbr_le e).trans hD_ge
    have hdeg : (gPoly u e).natDegree ≤ D_Z' - dy * (2 * e.1.2.2.1 + e.1.2.1) := by
      dsimp [gPoly]
      refine (natDegree_sum_le _ _).trans (Finset.sup_le fun t _ => ?_)
      have ht := t.isLt; dsimp [cap] at ht
      exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    omega
  have hf_wtd_ne := coord_wYZ_le_of_wYZ_ne hwYpos f_coord hf_wYZ
  have hlocal_van : ∀ i : ι,
      twOrdGE ((∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
        (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
        (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1)) m := by
    intro i
    have hNF_zero : ∀ idx : LocalBasisIdx m s,
        (∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) -
        (∑ b : LocalBasisIdx (m - k i) (s - d), vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) = 0 := by
      intro idx
      have hdeg1 : (∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx).natDegree ≤ D_Z' := by
        refine (natDegree_sum_le _ _).trans (Finset.sup_le fun e _ => natDegree_mul_le.trans ?_)
        have h1 := hg_wtd e
        have h2 := natDegree_kerDLocalNF_le_exact hwY1 (x i) (y i) (hy i) e idx
        omega
      have hdeg2 : (∑ b : LocalBasisIdx (m - k i) (s - d),
          vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx).natDegree ≤ D_Z' := by
        refine (natDegree_sum_le _ _).trans (Finset.sup_le fun b _ => natDegree_mul_le.trans ?_)
        have hv : (vPoly u i b).natDegree ≤ D_Z' - D_ZF :=
          (natDegree_sum_le _ _).trans (Finset.sup_le fun t _ =>
            (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp t.isLt))
        have hnf := natDegree_prodLocalNF_le_of_wYZ hwY1 (x i) (y i) (hy i) f_coord hf_wtd_ne b.1 idx
        omega
      have hdeg := (natDegree_sub_le _ _).trans (max_le hdeg1 hdeg2)
      ext t; rw [coeff_zero]
      by_cases ht : t < D_Z' + 1
      · exact congrFun hLu (i, idx, ⟨t, ht⟩)
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    have h1 : twOrdGE ((∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
        ∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) *
          localBasisElem idx.1) m := by
      have hrew : (∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
          ∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s, gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) *
            localBasisElem idx.1 =
          ∑ e : KerDIdx wY W s, locC (gPoly u e) *
            (kerDLocalPoly (C (x i)) (y i) e.1 -
              ∑ idx : LocalBasisIdx m s, locC (kerDLocalNF m s (C (x i)) (y i) e.1 idx) * localBasisElem idx.1) := by
        simp_rw [locC, map_sum, Finset.sum_mul]
        rw [Finset.sum_comm, ← Finset.sum_sub_distrib (G := LocalPoly (Polynomial F))]
        apply Finset.sum_congr rfl; intro e _
        have hms : ∀ a b c : LocalPoly (Polynomial F), a * (b - c) = a * b - a * c := fun a b c =>
          eq_sub_of_add_eq (G := LocalPoly (Polynomial F)) (by rw [← mul_add, sub_add_cancel (G := LocalPoly (Polynomial F))])
        rw [hms]; congr 1
        refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
        simp only [map_mul, mul_assoc]
      rw [hrew]; apply twOrdGE_sum; intro e _
      have hmem := (mem_kerDIdxFinset_iff wY W s hwYpos e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2).mp e.2
      simpa using twOrdGE_mul (twOrdGE_zero _)
        (twOrdGE_kerDLocalPoly_sub_NF m s (C (x i)) (y i) e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2 hmem.1 hmem.2.1)
    have h2 : twOrdGE ((∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
        (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) -
        ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k i) (s - d),
          vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1) m := by
      have hrew : (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
          (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) -
          ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k i) (s - d),
            vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1 =
          ∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) *
            ((∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) * localBasisElem b.1 -
              ∑ idx : LocalBasisIdx m s, locC (prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1) := by
        have h2a : (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) =
            ∑ b : LocalBasisIdx (m - k i) (s - d),
              (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
              (locC (vPoly u i b) * localBasisElem b.1) := Finset.mul_sum _ _ _
        have h2b : (∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k i) (s - d),
              vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1) =
            ∑ b : LocalBasisIdx (m - k i) (s - d), ∑ idx : LocalBasisIdx m s,
              locC (vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1 := by
          trans ∑ idx : LocalBasisIdx m s, ∑ b : LocalBasisIdx (m - k i) (s - d),
              locC (vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1
          · apply Finset.sum_congr rfl; intro idx _; unfold locC; simp only [map_sum, Finset.sum_mul]
          · exact Finset.sum_comm
        rw [h2a, h2b, ← Finset.sum_sub_distrib (G := LocalPoly (Polynomial F))]
        apply Finset.sum_congr rfl; intro b _
        have hms : ∀ a b' c : LocalPoly (Polynomial F), a * (b' - c) = a * b' - a * c := fun a b' c =>
          eq_sub_of_add_eq (G := LocalPoly (Polynomial F)) (by rw [← mul_add, sub_add_cancel (G := LocalPoly (Polynomial F))])
        rw [hms]
        refine congrArg₂ (· - ·) (by rw [← mul_assoc, mul_comm _ (locC (vPoly u i b)), mul_assoc]) ?_
        refine (Finset.sum_congr rfl fun idx _ => ?_).trans (Finset.mul_sum _ _ _).symm
        unfold locC; simp only [map_mul, mul_assoc]
      rw [hrew]; apply twOrdGE_sum; intro b _
      have hb := ((mem_localBasisFinset_iff (m - k i) (s - d) b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2).mp b.2).1
      simpa using twOrdGE_mul (twOrdGE_zero _)
        (twOrdGE_prodLocal_sub_NF hwYpos hd (C (x i)) (y i) f_coord b.1 hb)
    have hNF_eq : (∑ idx : LocalBasisIdx m s, locC (∑ e : KerDIdx wY W s,
        gPoly u e * kerDLocalNF m s (C (x i)) (y i) e.1 idx) * localBasisElem idx.1) =
        ∑ idx : LocalBasisIdx m s, locC (∑ b : LocalBasisIdx (m - k i) (s - d),
          vPoly u i b * prodLocalNF (C (x i)) (y i) f_coord b.1 idx) * localBasisElem idx.1 := by
      apply Finset.sum_congr rfl; intro idx _; rw [sub_eq_zero.mp (hNF_zero idx)]
    have hcomb := twOrdGE_sub h1 h2
    rwa [hNF_eq, sub_sub_sub_cancel_right] at hcomb
  have hGne : G ≠ 0 := by
    intro hG0
    have hg0 : ∀ e : KerDIdx wY W s, gPoly u e = 0 := by
      intro ⟨⟨k', r, b, a⟩, he⟩
      have hr := ((mem_kerDIdxFinset_iff wY W s hwYpos k' r b a).mp he).1
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hG0
        dsimp only [G] at h; rw [coeff_sum_kerDBasisPoly hwYpos, coeff_zero, coeff_zero, coeff_zero] at h
        simpa [he] using h
      · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hG0
        dsimp only [G] at h; rw [coeff_sum_kerDBasisPoly hwYpos, coeff_zero, coeff_zero, coeff_zero] at h
        have h1 : (2 * b + 1) % 2 = 1 := by omega
        have h2 : (2 * a) % 2 = 0 := by omega
        have h3 : (2 * b + 1) / 2 = b := by omega
        have h4 : (2 * a) / 2 = a := by omega
        simpa [h1, h2, h3, h4, he] using h
    have hv0 : ∀ i : ι, ∀ b : LocalBasisIdx (m - k i) (s - d), vPoly u i b = 0 := by
      intro i
      by_cases hkm : k i < m
      · have hloc := hlocal_van i
        simp only [hg0, locC, map_zero, zero_mul, Finset.sum_const_zero, zero_sub] at hloc
        have hneg : twOrdGE ((∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1)) m := by
          intro p q hpq; have := hloc p q hpq
          unfold twCoeff at this ⊢; rw [coeff_sub, coeff_sub, coeff_zero, coeff_zero] at this
          exact (sub_eq_zero.mp this).symm
        have hVvan : twOrdGE (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) (m - k i) := by
          by_contra hnot
          have hSpec := (hk_exact i).2 hkm
          have hfail := not_twOrdGE_mul_of_exact_ord hSpec.1 hSpec.2 hnot
          rw [Nat.add_sub_cancel' (le_of_lt hkm)] at hfail
          exact hfail hneg
        exact localBasis_linearIndependent_mod (m - k i) (s - d) (vPoly u i) hVvan
      · intro b; exfalso
        have hle := (hk_exact i).1
        have h0 : m - k i = 0 := by omega
        have hlt := ((mem_localBasisFinset_iff (m - k i) (s - d) b.1.1 b.1.2.1 b.1.2.2.1 b.1.2.2.2).mp b.2).2.1
        omega
    apply hu_ne; funext x'
    rcases x' with ⟨e, t⟩ | ⟨⟨i, b⟩, t⟩
    · have hc := hg0 e; dsimp only [gPoly] at hc
      have ht := congrArg (fun p : Polynomial F => p.coeff t.val) hc
      rw [finset_sum_coeff, coeff_zero, Finset.sum_eq_single t] at ht
      · simpa [coeff_C_mul, coeff_X_pow] using ht
      · intro t' _ hne; have : t'.val ≠ t.val := fun h => hne (Fin.ext h)
        simp [coeff_C_mul, coeff_X_pow, this.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hc := hv0 i b; dsimp only [vPoly] at hc
      have ht := congrArg (fun p : Polynomial F => p.coeff t.val) hc
      rw [finset_sum_coeff, coeff_zero, Finset.sum_eq_single t] at ht
      · simpa [coeff_C_mul, coeff_X_pow] using ht
      · intro t' _ hne; have : t'.val ≠ t.val := fun h => hne (Fin.ext h)
        simp [coeff_C_mul, coeff_X_pow, this.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hGmem : contactDeriv G = 0 ∧ G.natDegree ≤ s ∧ wdeg wY G ≤ W := by
    refine (mem_kerD_iff_exists_unique_coords hwY1 G).mpr ⟨gPoly u, rfl, ?_⟩
    intro c' hc'; funext ⟨⟨k', r, b, a⟩, he⟩
    have hr := ((mem_kerDIdxFinset_iff wY W s hwYpos k' r b a).mp he).1
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b)).coeff (2 * a)) hc'
      dsimp only [G] at h; rw [coeff_sum_kerDBasisPoly hwYpos, coeff_sum_kerDBasisPoly hwYpos] at h
      simpa [he] using h.symm
    · have h := congrArg (fun P : ContactPoly (Polynomial F) => ((P.coeff k').coeff (2 * b + 1)).coeff (2 * a)) hc'
      dsimp only [G] at h; rw [coeff_sum_kerDBasisPoly hwYpos, coeff_sum_kerDBasisPoly hwYpos] at h
      have h1 : (2 * b + 1) % 2 = 1 := by omega
      have h2 : (2 * a) % 2 = 0 := by omega
      have h3 : (2 * b + 1) / 2 = b := by omega
      have h4 : (2 * a) / 2 = a := by omega
      simpa [h1, h2, h3, h4, he] using h.symm
  have hwG : wYZ dy G ≤ D_Z' := wYZ_sum_kerDBasisPoly_le hwYpos (gPoly u) (fun e _ => hg_wtd e)
  refine ⟨G, hGne, hGmem.1, hGmem.2.1, hGmem.2.2, hwG, natDegree_Z_le_of_wYZ hwG, ?_, ?_, ⟨gPoly u, vPoly u, rfl, hlocal_van⟩⟩
  · -- F ∤ G over RatFunc F: immediate from wdeg wY (liftC G) ≤ W < W_F = wdeg wY (liftC F)!
    rintro ⟨Q', hQ'0⟩
    have hQ' : liftC G = liftC Fpoly * Q' := hQ'0
    have hinj := IsFractionRing.injective (Polynomial F) (RatFunc F)
    have hGne_rat : liftC G ≠ 0 := by
      intro h0; apply hGne
      refine Polynomial.ext fun k' => Polynomial.ext fun j' => Polynomial.ext fun i' => ?_
      have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff j').coeff i') h0
      simp only [liftC, coe_mapRingHom, coeff_map, coeff_zero] at h
      exact hinj (by simp only [coeff_zero, map_zero]; exact h)
    have hFne_rat : liftC Fpoly ≠ 0 := by
      intro h0; apply hFne
      refine Polynomial.ext fun k' => Polynomial.ext fun j' => Polynomial.ext fun i' => ?_
      have h := congrArg (fun P : ContactPoly (RatFunc F) => ((P.coeff k').coeff j').coeff i') h0
      simp only [liftC, coe_mapRingHom, coeff_map, coeff_zero] at h
      exact hinj (by simp only [coeff_zero, map_zero]; exact h)
    have hQ'ne : Q' ≠ 0 := by intro h0; rw [h0, mul_zero] at hQ'; exact hGne_rat hQ'
    have hGw_rat : wdeg wY (liftC G) ≤ W := by
      rw [wdeg_le_iff]; intro k' j' i' hnz
      simp only [liftC, coe_mapRingHom, coeff_map] at hnz
      have hnz' : ((G.coeff k').coeff j').coeff i' ≠ 0 := fun h0 => hnz (by rw [h0, map_zero])
      exact (wdeg_le_iff wY W G).mp hGmem.2.2 k' j' i' hnz'
    have hFw_rat : W_F ≤ wdeg wY (liftC Fpoly) := by
      rw [← hFwdeg, wdeg_le_iff]; intro k' j' i' hnz
      have hnz' : (((liftC Fpoly).coeff k').coeff j').coeff i' ≠ 0 := by
        simp only [liftC, coe_mapRingHom, coeff_map]; intro h0; exact hnz (hinj (by rw [map_zero]; exact h0))
      exact (wdeg_le_iff wY (wdeg wY (liftC Fpoly)) (liftC Fpoly)).mp le_rfl k' j' i' hnz'
    have hmul := wdeg_mul wY hFne_rat hQ'ne
    rw [← hQ'] at hmul
    omega
  · -- Evaluation vanishing (identical to exists_quotient_contact_interpolant_wtd)
    intro A' hWlt z P hP Az hAz hagree hFvan
    by_contra hGvan
    let E := evalContact (evalZContact G z) P
    have hdvd_each : ∀ i ∈ Az, ((Polynomial.X : Polynomial F) - Polynomial.C (x i)) ^ (2 * m) ∣ E := by
      intro i hi
      have hloc_z := twOrdGE_evalZLocal (hlocal_van i) z
      have hdvd := pow_two_mul_dvd_evalLocal_of_twOrdGE (x i) ((y i).eval z) P (hagree i hi) hloc_z
      have hEv : evalLocal (x i) ((y i).eval z) P
          (evalZLocal ((∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
            (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1)) z) = E := by
        have hsub : evalZLocal ((∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) -
            (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) *
            (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1)) z =
            evalZLocal (∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) z -
            evalZLocal (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) z *
            evalZLocal (∑ b : LocalBasisIdx (m - k i) (s - d), locC (vPoly u i b) * localBasisElem b.1) z := by
          rw [← evalZLocal_mul]
          exact eq_sub_of_add_eq (G := LocalPoly F)
            (by rw [← evalZLocal_add, sub_add_cancel (G := LocalPoly (Polynomial F))])
        rw [hsub, map_sub, map_mul]
        have hEvG : evalLocal (x i) ((y i).eval z) P
            (evalZLocal (∑ e : KerDIdx wY W s, locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) z) = E := by
          dsimp only [E, G]
          rw [show evalZLocal (∑ e : KerDIdx wY W s, _) z = ∑ e : KerDIdx wY W s,
                evalZLocal (locC (gPoly u e) * kerDLocalPoly (C (x i)) (y i) e.1) z
                from by unfold evalZLocal; simp [Polynomial.map_sum],
              show evalZContact (∑ e : KerDIdx wY W s, _) z = ∑ e : KerDIdx wY W s,
                evalZContact (cC (gPoly u e) * kerDBasisPoly e.1) z
                from by unfold evalZContact; simp [Polynomial.map_sum],
              map_sum, evalContact_sum]
          apply Finset.sum_congr rfl; intro e _
          rw [evalZLocal_mul, evalZLocal_locC, evalZLocal_kerDLocalPoly, map_mul, evalLocal_locC,
            evalLocal_kerDLocalPoly,
            show evalZContact (_ * _) z = evalZContact (cC (gPoly u e)) z * evalZContact (kerDBasisPoly e.1) z
              from by unfold evalZContact; simp [Polynomial.map_mul],
            evalZContact_cC, evalZContact_kerDBasisPoly, evalContact_mul, evalContact_cC]
        have hEvF : evalLocal (x i) ((y i).eval z) P
            (evalZLocal (∑ e1 : KerDIdx wY W_F d, locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) z) = 0 := by
          rw [show evalZLocal (∑ e1 : KerDIdx wY W_F d, _) z = ∑ e1 : KerDIdx wY W_F d,
                evalZLocal (locC (f_coord e1) * kerDLocalPoly (C (x i)) (y i) e1.1) z
                from by unfold evalZLocal; simp [Polynomial.map_sum], map_sum]
          trans evalContact (evalZContact Fpoly z) P
          · dsimp only [Fpoly]
            rw [show evalZContact (∑ e1 : KerDIdx wY W_F d, _) z = ∑ e1 : KerDIdx wY W_F d,
                  evalZContact (cC (f_coord e1) * kerDBasisPoly e1.1) z
                  from by unfold evalZContact; simp [Polynomial.map_sum], evalContact_sum]
            apply Finset.sum_congr rfl; intro e1 _
            rw [evalZLocal_mul, evalZLocal_locC, evalZLocal_kerDLocalPoly, map_mul, evalLocal_locC,
              evalLocal_kerDLocalPoly,
              show evalZContact (_ * _) z = evalZContact (cC (f_coord e1)) z * evalZContact (kerDBasisPoly e1.1) z
                from by unfold evalZContact; simp [Polynomial.map_mul],
              evalZContact_cC, evalZContact_kerDBasisPoly, evalContact_mul, evalContact_cC]
          · exact hFvan
        rw [hEvG, hEvF, zero_mul, sub_zero]
      rwa [hEv] at hdvd
    have hdvd_prod : (∏ i ∈ Az, ((Polynomial.X : Polynomial F) - Polynomial.C (x i)) ^ (2 * m)) ∣ E := by
      apply Finset.prod_dvd_of_coprime
      · intro i _ j _ hij
        apply IsCoprime.pow
        have hne_x : x i ≠ x j := fun h => hij (x.injective h)
        refine ⟨Polynomial.C (x j - x i)⁻¹, -Polynomial.C (x j - x i)⁻¹, ?_⟩
        have hne' : x j - x i ≠ 0 := sub_ne_zero.mpr hne_x.symm
        calc Polynomial.C (x j - x i)⁻¹ * ((Polynomial.X : Polynomial F) - Polynomial.C (x i)) +
              -Polynomial.C (x j - x i)⁻¹ * ((Polynomial.X : Polynomial F) - Polynomial.C (x j))
            = Polynomial.C (x j - x i)⁻¹ * Polynomial.C (x j - x i) := by rw [map_sub]; ring
          _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hne', map_one]
      · exact hdvd_each
    have hdeg_prod : (∏ i ∈ Az, ((Polynomial.X : Polynomial F) - Polynomial.C (x i)) ^ (2 * m)).natDegree = Az.card * (2 * m) := by
      rw [natDegree_prod _ _ (fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _))]
      simp [natDegree_pow, natDegree_X_sub_C]
    have hle_deg : Az.card * (2 * m) ≤ E.natDegree := by
      rw [← hdeg_prod]; exact natDegree_le_of_dvd hdvd_prod hGvan
    have hE_deg : E.natDegree ≤ W := by
      apply natDegree_evalContact_le wY W hwY1 _ P hP
      rw [wdeg_le_iff]; intro k' j' i' hnz
      have hmem : evalZContact G z = ∑ e : KerDIdx wY W s, cC ((gPoly u e).eval z) * kerDBasisPoly e.1 := by
        dsimp only [G]; unfold evalZContact; simp only [Polynomial.map_sum, Polynomial.map_mul]
        apply Finset.sum_congr rfl; intro e _
        change evalZContact (cC (gPoly u e)) z * evalZContact (kerDBasisPoly e.1) z = _
        rw [evalZContact_cC, evalZContact_kerDBasisPoly]
      rw [hmem, coeff_sum_kerDBasisPoly hwYpos] at hnz
      by_cases h00 : j' % 2 = 0 ∧ i' % 2 = 0
      · simp only [h00, and_self, ↓reduceIte] at hnz
        split_ifs at hnz with hm1
        · have hw := ((mem_kerDIdxFinset_iff wY W s hwYpos _ _ _ _).mp hm1).2.2
          have hj2 : 2 * (j' / 2) = j' := by omega
          have hi2 : 2 * (i' / 2) = i' := by omega
          nlinarith only [hw, hj2, hi2]
        · exact absurd rfl hnz
      · simp only [h00, ↓reduceIte] at hnz
        by_cases h10 : j' % 2 = 1 ∧ i' % 2 = 0
        · simp only [h10, and_self, ↓reduceIte] at hnz
          split_ifs at hnz with hm2
          · have hw := ((mem_kerDIdxFinset_iff wY W s hwYpos _ _ _ _).mp hm2).2.2
            have hj2 : 2 * (j' / 2) + 1 = j' := by omega
            have hi2 : 2 * (i' / 2) = i' := by omega
            nlinarith only [hw, hj2, hi2]
          · exact absurd rfl hnz
        · simp only [h10, ↓reduceIte] at hnz
          by_cases h01 : j' % 2 = 0 ∧ i' % 2 = 1 ∧ 0 < k'
          · simp only [h01, and_self, ↓reduceIte] at hnz
            split_ifs at hnz with hm3
            · have hw := ((mem_kerDIdxFinset_iff wY W s hwYpos _ _ _ _).mp hm3).2.2
              have hj2 : 2 * (j' / 2) = j' := by omega
              have hi2 : 2 * (i' / 2) + 1 = i' := by omega
              have hk1 : (k' - 1) * (wY - 1) + 1 * wY = k' * (wY - 1) + 1 := by zify [hwY1, h01.2.2]; ring
              nlinarith only [hw, hj2, hi2, hk1]
            · exact absurd rfl hnz
          · simp only [h01, ↓reduceIte] at hnz; exact absurd rfl hnz
    nlinarith only [hWlt, hAz, hle_deg, hE_deg]

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

private lemma sum_v_cast {A : Type*} [CommRing A] {n1 n2 s : ℕ} (h : n1 = n2)
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
    (hbad : ∀ z ∈ S, BadOn6401 u₀ u₁ (Az z))
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
  exact hΦgap_of_g_hi u₀ u₁ q₀ W_F m s hiGNum hiGDen hhiGD Φ hWΦ_1 (by simpa using hWF_lo) k hord_k (Az z) (hG_hi z hz)

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

/-! ### Part 5: Kernel-`decide` Verification That No Table 4 `hiG = 1` Bucket Uses `useP64` -/

def binNoP64AtHi1 (bin : T4BinCert) : Bool :=
  bin.buckets.all fun b => !(b.hiGNum == b.hiGDen) || (!b.cap1.useP64 && !b.cap2.useP64)

theorem t4a_hi1_no_p64 (br : T4ABranch)
    (hvalid : match br with
      | .det | .p0Zero => True
      | .p0 m21Nz _ p0M10D4 q2M21M10 => m21Nz = false → p0M10D4 = true ∧ q2M21M10 = false
      | .b1c1 _ _ bCase => bCase < 6) :
    (t4aBins br).all binNoP64AtHi1 = true := by
  cases br with
  | det => decide
  | p0Zero => decide
  | p0 m21Nz rGt p0M10D4 q2M21M10 =>
      cases m21Nz <;> cases rGt <;> cases p0M10D4 <;> cases q2M21M10
      all_goals first | decide | (exfalso; have := hvalid rfl; simp at this)
  | b1c1 rGt r4g4 bCase =>
      cases rGt <;> cases r4g4 <;>
        (rcases (show bCase = 0 ∨ bCase = 1 ∨ bCase = 2 ∨ bCase = 3 ∨ bCase = 4 ∨ bCase = 5 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem t4b1_hi1_no_p64 (br : T4BBranch) (hr : br.rGt = false) (hq1 : br.q1Case < 3) (hode : br.odeCase < 7) :
    (t4b1Bins br).all binNoP64AtHi1 = true := by
  rcases br with ⟨rGt, vCan, q1Case, odeCase⟩
  dsimp only at hr hq1 hode; subst hr
  cases vCan <;>
    (rcases (show q1Case = 0 ∨ q1Case = 1 ∨ q1Case = 2 by omega) with rfl | rfl | rfl) <;>
    (rcases (show odeCase = 0 ∨ odeCase = 1 ∨ odeCase = 2 ∨ odeCase = 3 ∨ odeCase = 4 ∨ odeCase = 5 ∨ odeCase = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem t4b2_hi1_no_p64 (br : T4BBranch) (hr : br.rGt = true) (hq1 : br.q1Case < 3) (hode : br.odeCase < 7) :
    (t4b2Bins br).all binNoP64AtHi1 = true := by
  rcases br with ⟨rGt, vCan, q1Case, odeCase⟩
  dsimp only at hr hq1 hode; subst hr
  cases vCan <;>
    (rcases (show q1Case = 0 ∨ q1Case = 1 ∨ q1Case = 2 by omega) with rfl | rfl | rfl) <;>
    (rcases (show odeCase = 0 ∨ odeCase = 1 ∨ odeCase = 2 ∨ odeCase = 3 ∨ odeCase = 4 ∨ odeCase = 5 ∨ odeCase = 6 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

lemma no_p64_of_binNoP64AtHi1 {bin : T4BinCert} (h : binNoP64AtHi1 bin = true)
    {b : T4BucketCert} (hb : b ∈ bin.buckets) (hhi : b.hiGNum = b.hiGDen) :
    b.cap1.useP64 = false ∧ b.cap2.useP64 = false := by
  have hb' := List.all_eq_true.mp h b hb
  simp only [hhi, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hb'
  exact hb'

end B6401QuotBridge
end ProximityPrize.SubmissionBinaryLower
