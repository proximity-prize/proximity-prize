import ProximityPrize.SubmissionBinaryLower.Binary6402SmallAlg
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

end B6402QuotBridge
end ProximityPrize.SubmissionBinaryLower
