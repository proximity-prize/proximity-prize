import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import ProximityPrize.SubmissionBinaryLower.Binary6402FarkasVerifier
import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid12
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

/-!
# Fast Pure-`Int` Kernel-Decidable Certificate Verifiers & Soundness Theorems (Binary 64.01)

Provides zero-`Nat.gcd`, pure-`Int` boolean checkers (`decide`-compatible, ZERO `native_decide`)
and 100% formal soundness proofs connecting directly to:
- `B6401ContactKerD.varsKerDUpperQ` & `B6402FarkasVerifier.vquotLbQ`,
- `B6402HybridP64.card_le_of_biPoly_pow` & `B6402HybridP64.hybrid_p64_card_le`,
- Sparse integer Farkas duality for ALL 116 Table 4 branches (both infeasibility and single-`(m, s)` surplus),
- Compact integer-weight dual certificates for Tables 1, 2, and 3!
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402IntFarkas

open B6401Params B6401ContactKerD B6401ResultantOrd B6402FarkasVerifier B6402HybridP64
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary BCHKSSubstitutionVanish P64Cofactor P64LineOrder
open scoped BigOperators

/-! ### Part 1: Exact `Int` Numerator/Denominator for `varsKerDUpperQ` and `vquotLbQ` -/

/-- Exact integer numerator of `varsKerDUpperQ wY (Wnum / Wden) s` over denominator `8 * wY * Wden^2`. -/
def varsKerDUpperNum (wY s : ℕ) (Wnum Wden : ℤ) : ℤ :=
  (List.range (s + 1)).foldl (fun acc k =>
    (List.range 2).foldl (fun acc2 r =>
      if k + r ≤ s then
        let uN : ℤ := Wnum - ((k * (wY - 1) + r * wY : ℕ) : ℤ) * Wden
        let u1N : ℤ := max 0 (uN + (wY : ℤ) * Wden)
        let u0N : ℤ := max 0 uN
        acc2 + (u1N * u1N + 4 * Wden * u0N + 8 * (wY : ℤ) * Wden * Wden)
      else acc2) acc) 0

private lemma list_foldl_add {α : Type*} (l : List α) (f : α → ℤ) (init : ℤ) :
    l.foldl (fun acc x => acc + f x) init = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
      ring

private lemma list_sum_range_eq_finset_sum (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

lemma varsKerDUpperNum_eq (wY s : ℕ) (hwY : 0 < wY) (Wnum Wden : ℤ) (hden : 0 < Wden) :
    (varsKerDUpperNum wY s Wnum Wden : ℚ) / ((8 * (wY : ℤ) * Wden * Wden : ℤ) : ℚ) =
      varsKerDUpperQ wY ((Wnum : ℚ) / (Wden : ℚ)) s := by
  have hwQ : (0 : ℚ) < (wY : ℚ) := by exact_mod_cast hwY
  have hdQ : (0 : ℚ) < (Wden : ℚ) := by exact_mod_cast hden
  -- Rewrite nested foldl to Finset double sum!
  let term (k r : ℕ) : ℤ :=
    if k + r ≤ s then
      let uN : ℤ := Wnum - ((k * (wY - 1) + r * wY : ℕ) : ℤ) * Wden
      let u1N : ℤ := max 0 (uN + (wY : ℤ) * Wden)
      let u0N : ℤ := max 0 uN
      u1N * u1N + 4 * Wden * u0N + 8 * (wY : ℤ) * Wden * Wden
    else 0
  have hfold : varsKerDUpperNum wY s Wnum Wden =
      ∑ k ∈ Finset.range (s + 1), ∑ r ∈ Finset.range 2, term k r := by
    unfold varsKerDUpperNum
    have hinner : ∀ (acc : ℤ) (k : ℕ),
        (List.range 2).foldl (fun acc2 r =>
          if k + r ≤ s then
            let uN : ℤ := Wnum - ((k * (wY - 1) + r * wY : ℕ) : ℤ) * Wden
            let u1N : ℤ := max 0 (uN + (wY : ℤ) * Wden)
            let u0N : ℤ := max 0 uN
            acc2 + (u1N * u1N + 4 * Wden * u0N + 8 * (wY : ℤ) * Wden * Wden)
          else acc2) acc =
        acc + ∑ r ∈ Finset.range 2, term k r := by
      intro acc k
      have hite : ∀ (acc2 : ℤ) (r : ℕ),
          (if k + r ≤ s then
            let uN : ℤ := Wnum - ((k * (wY - 1) + r * wY : ℕ) : ℤ) * Wden
            let u1N : ℤ := max 0 (uN + (wY : ℤ) * Wden)
            let u0N : ℤ := max 0 uN
            acc2 + (u1N * u1N + 4 * Wden * u0N + 8 * (wY : ℤ) * Wden * Wden)
          else acc2) = acc2 + term k r := fun acc2 r => by dsimp [term]; split_ifs <;> ring
      simp_rw [hite]
      rw [list_foldl_add, list_sum_range_eq_finset_sum]
    simp_rw [hinner]
    rw [list_foldl_add, list_sum_range_eq_finset_sum, zero_add]
  rw [hfold, Int.cast_sum, Finset.sum_div]
  unfold varsKerDUpperQ
  apply Finset.sum_congr rfl; intro k _
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl; intro r _
  dsimp only [term]
  split_ifs with hkr
  · set c : ℕ := k * (wY - 1) + r * wY
    have hu : (Wnum : ℚ) / (Wden : ℚ) - (c : ℚ) = ((Wnum - (c : ℤ) * Wden : ℤ) : ℚ) / (Wden : ℚ) := by
      push_cast; field_simp [hdQ.ne']
    have hu1 : max (0 : ℚ) (((Wnum - (c : ℤ) * Wden : ℤ) : ℚ) / (Wden : ℚ) + (wY : ℚ)) =
        ((max (0 : ℤ) (Wnum - (c : ℤ) * Wden + (wY : ℤ) * Wden) : ℤ) : ℚ) / (Wden : ℚ) := by
      have hadd : ((Wnum - (c : ℤ) * Wden : ℤ) : ℚ) / (Wden : ℚ) + (wY : ℚ) =
          ((Wnum - (c : ℤ) * Wden + (wY : ℤ) * Wden : ℤ) : ℚ) / (Wden : ℚ) := by
        push_cast; field_simp [hdQ.ne']
      rw [hadd, Int.cast_max, Int.cast_zero]
      by_cases h0 : (0 : ℚ) ≤ ((Wnum - (c : ℤ) * Wden + (wY : ℤ) * Wden : ℤ) : ℚ)
      · have h0d : (0 : ℚ) ≤ ((Wnum - (c : ℤ) * Wden + (wY : ℤ) * Wden : ℤ) : ℚ) / (Wden : ℚ) :=
          div_nonneg h0 hdQ.le
        rw [max_eq_right h0, max_eq_right h0d]
      · have h0' : ((Wnum - (c : ℤ) * Wden + (wY : ℤ) * Wden : ℤ) : ℚ) ≤ 0 := le_of_not_ge h0
        have h0d : ((Wnum - (c : ℤ) * Wden + (wY : ℤ) * Wden : ℤ) : ℚ) / (Wden : ℚ) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg h0' hdQ.le
        rw [max_eq_left h0', max_eq_left h0d, zero_div]
    have hu0 : max (0 : ℚ) (((Wnum - (c : ℤ) * Wden : ℤ) : ℚ) / (Wden : ℚ)) =
        ((max (0 : ℤ) (Wnum - (c : ℤ) * Wden) : ℤ) : ℚ) / (Wden : ℚ) := by
      rw [Int.cast_max, Int.cast_zero]
      by_cases h0 : (0 : ℚ) ≤ ((Wnum - (c : ℤ) * Wden : ℤ) : ℚ)
      · have h0d : (0 : ℚ) ≤ ((Wnum - (c : ℤ) * Wden : ℤ) : ℚ) / (Wden : ℚ) :=
          div_nonneg h0 hdQ.le
        rw [max_eq_right h0, max_eq_right h0d]
      · have h0' : ((Wnum - (c : ℤ) * Wden : ℤ) : ℚ) ≤ 0 := le_of_not_ge h0
        have h0d : ((Wnum - (c : ℤ) * Wden : ℤ) : ℚ) / (Wden : ℚ) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg h0' hdQ.le
        rw [max_eq_left h0', max_eq_left h0d, zero_div]
    rw [hu, hu1, hu0]
    push_cast
    field_simp [hwQ.ne', hdQ.ne']
    ring
  · simp

/-- Exact integer numerator of `vquotLbQ d m s (cNum / cDen)` over `vquotDen m cDen`. -/
def vquotNum (d m s : ℕ) (cNum cDen : ℤ) : ℤ :=
  let W : ℕ := 2 * B6402HybridP64.A * m - 1
  (varsKerDExact wY W s : ℤ) * (8 * (wY : ℤ) * cDen * cDen) -
    varsKerDUpperNum wY (s - d) ((W : ℤ) * cDen - cNum * (wY : ℤ)) cDen

/-- Exact positive denominator of `vquotLbQ d m s (cNum / cDen)`. -/
def vquotDen (m : ℕ) (cDen : ℤ) : ℤ :=
  (N : ℤ) * (m : ℤ) * (m : ℤ) * (8 * (wY : ℤ) * cDen * cDen)

lemma vquotDen_pos {m : ℕ} {cDen : ℤ} (hm : 0 < m) (hden : 0 < cDen) :
    0 < vquotDen m cDen := by
  unfold vquotDen
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hN : (0 : ℤ) < N := by norm_num [N]
  have hwY : (0 : ℤ) < wY := by norm_num [wY]
  positivity

lemma vquotNum_div_eq (d m s : ℕ) (hm : 0 < m) (cNum cDen : ℤ) (hden : 0 < cDen) :
    (vquotNum d m s cNum cDen : ℚ) / (vquotDen m cDen : ℚ) =
      vquotLbQ d m s ((cNum : ℚ) / (cDen : ℚ)) := by
  have hwY : 0 < wY := by norm_num [wY]
  have hwQ : (0 : ℚ) < (wY : ℚ) := by exact_mod_cast hwY
  have hdQ : (0 : ℚ) < (cDen : ℚ) := by exact_mod_cast hden
  have hNm2 : (0 : ℚ) < (N : ℚ) * (m : ℚ) * (m : ℚ) := by
    have hN : (0 : ℚ) < N := by norm_num [N]
    have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  have h8 : (0 : ℚ) < ((8 * (wY : ℤ) * cDen * cDen : ℤ) : ℚ) := by push_cast; positivity
  unfold vquotLbQ vquotNum vquotDen
  dsimp only
  set W : ℕ := 2 * B6402HybridP64.A * m - 1
  have hW : ((W : ℕ) : ℚ) - (cNum : ℚ) / (cDen : ℚ) * (wY : ℚ) =
      (((W : ℤ) * cDen - cNum * (wY : ℤ) : ℤ) : ℚ) / (cDen : ℚ) := by
    push_cast; field_simp [hdQ.ne']
  rw [hW, ← varsKerDUpperNum_eq wY (s - d) hwY _ cDen hden]
  push_cast
  field_simp [hNm2.ne', hwQ.ne', hdQ.ne']

/-! ### Part 2: Pure-`Int` Affine Cap Checker (`card_le_of_biPoly_pow` & `hybrid_p64_card_le`) -/

/-- Exact integer ceiling `⌈p / q⌉` for `p : ℕ`, `q : ℕ` (`q > 0`). -/
def ceilDivNat (p q : ℕ) : ℕ := (p + q - 1) / q

lemma le_ceilDivNat_mul (p q : ℕ) (hq : 0 < q) : p ≤ ceilDivNat p q * q := by
  unfold ceilDivNat
  have h := Nat.div_add_mod (p + q - 1) q
  have hmod : (p + q - 1) % q < q := Nat.mod_lt _ hq
  rw [mul_comm] at h
  omega

lemma ceil_rat_le_ceilDivNat (p q : ℕ) (hq : 0 < q) : (p : ℚ) / (q : ℚ) ≤ (ceilDivNat p q : ℚ) := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  rw [div_le_iff₀ hqQ]
  exact_mod_cast le_ceilDivNat_mul p q hq

/-- Pure-`ℕ`/`ℤ` checker verifying that the affine ArkLib or Hybrid-P64 bound for a single `(m, s)`
with surplus `≥ δNum / δDen`, weight upper bound `cHiNum / cHiDen`, gap upper bound `hiGNum / hiGDen`,
power `q₀ ∈ {1, 2}`, satisfies:
  `∀ D_ZF, |S| ≤ c1Bkt * D_ZF + c0Bkt`!
When `useP64 = true`, ALSO verifies all 17 side conditions of `B6402HybridP64.hybrid_p64_card_le`
with explicit integer witnesses `(h0, q_aux, slack, P0, M0, Cd, Ch)`! -/
structure CapWitness where
  useP64 : Bool
  h0 : ℕ
  q_aux : ℕ
  slack : ℕ
  P0 : ℕ
  M0 : ℕ
  Cd : ℕ
  Ch : ℕ
  c1Bkt : ℕ
  c0Bkt : ℕ
  deriving Repr

/-- Helper: pure-`ℕ` check of the 4 affine linear-cap inequalities. -/
def checkLinearCap (d m s W I0 rkSd δNum δDen q₀ c1Bkt c0Bkt kHNum kHDen k0Num k0Den : ℕ) : Bool :=
  decide (kHNum * (d + s) ≤ c1Bkt * kHDen) &&
  decide (kHNum * (d * rkSd * δDen + s * m * m * δNum) ≤ c1Bkt * kHDen * m * m * δNum) &&
  decide (kHNum * (d * q₀ * (W / wY)) * k0Den + k0Num * kHDen ≤ c0Bkt * kHDen * k0Den) &&
  decide (kHNum * d * (q₀ * (W / wY) * I0 * δDen + N * m * m * δNum) * k0Den +
    k0Num * kHDen * N * m * m * δNum ≤ c0Bkt * kHDen * k0Den * N * m * m * δNum)

private lemma checkLinearCap_mp {d m s W I0 rkSd δNum δDen q₀ c1Bkt c0Bkt kHNum kHDen k0Num k0Den : ℕ}
    (h : checkLinearCap d m s W I0 rkSd δNum δDen q₀ c1Bkt c0Bkt kHNum kHDen k0Num k0Den = true) :
    (kHNum * (d + s) ≤ c1Bkt * kHDen) ∧
    (kHNum * (d * rkSd * δDen + s * m * m * δNum) ≤ c1Bkt * kHDen * m * m * δNum) ∧
    (kHNum * (d * q₀ * (W / wY)) * k0Den + k0Num * kHDen ≤ c0Bkt * kHDen * k0Den) ∧
    (kHNum * d * (q₀ * (W / wY) * I0 * δDen + N * m * m * δNum) * k0Den +
      k0Num * kHDen * N * m * m * δNum ≤ c0Bkt * kHDen * k0Den * N * m * m * δNum) := by
  unfold checkLinearCap at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- Helper: pure-`ℕ` check of all 22 side conditions of `B6402HybridP64.hybrid_p64_card_le`! -/
def checkSideP64 (d m B W_Phi DeltaMax q₀ : ℕ) (w : CapWitness) : Bool :=
  let M_W : ℕ := (4 * W_Phi) / wY
  let N_eff : ℕ := (B6402HybridP64.A - wY) + DeltaMax
  let tNum : ℕ := N - wY
  let tDen : ℕ := B6402HybridP64.A - wY
  let psi0 : ℕ := 1 + (2 * wY - 1) * (2 * w.h0 - 1) + 2 * (w.h0 - (2 * wY + 1))
  (d == 1) && (q₀ == 1 || q₀ == 2) &&
  (2 * B * W_Phi < 2 ^ 64) &&
  ((M_W + B) * (4 * W_Phi) < 2 ^ 64) &&
  (1 ≤ w.h0) && (1 ≤ w.q_aux) && (0 < w.M0) &&
  (B ≤ 2 * m * (w.h0 + 1)) &&
  (B6402HybridP64.A + 4 * DeltaMax + 1 ≤ 4 * (w.h0 + 1) * wY) &&
  (4 * B ≤ w.q_aux) &&
  (M_W * (8 * N) ≤ w.q_aux * w.slack) &&
  (8 * wY * w.slack * (w.h0 + 1) ^ 2 +
    16 * wY * (B6402HybridP64.A - wY + 10000) * (w.h0 + 1) + (wY + 2) ^ 2 ≤
    64 * wY * w.P0 * (w.h0 + 1) ^ 2) &&
  (w.M0 + w.P0 == B6402HybridP64.A - wY) &&
  (2 * N_eff ≤ w.M0 * (w.h0 + 1)) &&
  ((2 * w.h0 - 1) * tDen + tNum * psi0 ≤ w.Cd * tDen) &&
  (208984 ≤ w.Cd) &&
  (2 * N_eff * N * 6 + N * w.M0 ≤ w.Cd * w.M0) &&
  (16 * N_eff * N + N * 10000 ^ 2 ≤ w.Cd * 10000 ^ 2) &&
  (q₀ * (w.q_aux + M_W) ≤ w.Ch) &&
  (120000000000 ≤ w.Ch * (w.h0 + 1)) &&
  (q₀ * (tNum + (N - wY - 1) * tDen) ≤ w.Ch * tDen) &&
  (2 * N_eff * N * (2 * q₀ + 2) ≤ w.Ch * w.M0) &&
  (2 * N_eff * (4 * q₀ + 1) ≤ w.Ch * 10000)

/-- Exact `ℕ` check of the linear coefficient `kH` and constant `k0` from `CapWitness`,
plus affine verification `kH * aH ≤ c1Bkt` and `kH * bH + k0 ≤ c0Bkt`! -/
def checkCapWitness (d m s cHiNum cHiDen δNum δDen hiGNum hiGDen q₀ : ℕ) (w : CapWitness) : Bool :=
  if m == 0 || s < d || cHiDen == 0 || δNum == 0 || δDen == 0 || hiGDen == 0 then false
  else
    let W : ℕ := 2 * B6402HybridP64.A * m - 1
    let cHiWY : ℕ := ceilDivNat (cHiNum * wY) cHiDen
    let Wsub : ℕ := W - cHiWY
    let I0 : ℕ := varsKerDExact wY W s - varsKerDExact wY Wsub (s - d)
    let rkSd : ℕ := rankKerD m (s - d)
    let W_Phi : ℕ := d * W + s * (cHiWY - d * (wY - 1))
    let B : ℕ := W_Phi / wY
    if !w.useP64 then
      let tNum : ℕ := N - wY
      let tDen : ℕ := B6402HybridP64.A - wY
      let psi : ℕ := 1 + (2 * wY - 1) * (2 * B - 1) + 2 * (B - (2 * wY + 1))
      let kHNum := (2 * B - 1) * tDen + tNum * psi
      let k0Num := tNum * q₀ * B + q₀ * (N - wY - 1) * B * tDen
      decide (1 ≤ B) && checkLinearCap d m s W I0 rkSd δNum δDen q₀ w.c1Bkt w.c0Bkt kHNum tDen k0Num tDen
    else
      let DeltaMax : ℕ := (s * hiGNum * N) / hiGDen
      let M_W : ℕ := (4 * W_Phi) / wY
      let M_B : ℕ := max M_W (4 * B)
      let kH : ℕ := w.Cd + M_B + B + 1
      let k0 : ℕ := (w.Cd + M_B + B) * q₀ * B + w.Ch * B
      checkSideP64 d m B W_Phi DeltaMax q₀ w &&
        checkLinearCap d m s W I0 rkSd δNum δDen q₀ w.c1Bkt w.c0Bkt kH 1 k0 1

private lemma checkSideP64_card_le
    (u₀ u₁ : Idx → Fld) (d m B H W_Phi DeltaMax q₀ : ℕ) (w : CapWitness)
    (hq₀ : q₀ = 1 ∨ q₀ = 2)
    (hside_b : checkSideP64 d m B W_Phi DeltaMax q₀ w = true)
    (Φ : Polynomial (Polynomial (Polynomial Fld)))
    (hΦ : Φ ≠ 0)
    (hWΦ : P64Caps.Weighted.weightedSupportDegree Φ wY ≤ W_Phi)
    (hB : Φ.natDegree ≤ B)
    (hH : ∀ j a, ((Φ.coeff j).coeff a).natDegree ≤ H)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval Φ z (P z) = 0)
    (hcard : ∀ z ∈ S, B6402HybridP64.A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6402 u₀ u₁ (Az z))
    (hΦgap : ∀ z ∈ S,
      (P64Caps.Weighted.weightedSupportDegree Φ wY : ℤ) -
        (∑ i ∈ Az z, (P64LineOrder.lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
        (2 * m : ℤ) * ((Az z).card - (B6402HybridP64.A : ℤ)) ≤ (DeltaMax : ℤ)) :
    (S.card : ℚ) ≤
      (((w.Cd + max ((4 * W_Phi) / wY) (4 * B) + B + 1 : ℕ) : ℚ) / (1 : ℕ)) * (H : ℚ) +
      ((((w.Cd + max ((4 * W_Phi) / wY) (4 * B) + B) * q₀ * B + w.Ch * B : ℕ) : ℚ) / (1 : ℕ)) := by
  unfold checkSideP64 at hside_b
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hside_b
  rcases hside_b with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hFΦ⟩, hFaux⟩, hh0⟩, hqaux⟩, hM0pos⟩, hBmul⟩, hC0h⟩, h4Bq⟩,
    hslack⟩, hP0⟩, hM0eq⟩, hMh⟩, hCd_ark⟩, hCd_light⟩, hCd_c7⟩, hCd_c6⟩, hCh_aux⟩, hCh_light⟩,
    hCh_ark⟩, hCh_c7⟩, hCh_c6⟩
  set M_W : ℕ := (4 * W_Phi) / wY
  set M_B : ℕ := max M_W (4 * B)
  set N_eff : ℕ := (B6402HybridP64.A - wY) + DeltaMax
  set tNum : ℕ := N - wY
  set tDen : ℕ := B6402HybridP64.A - wY
  have htDen : 0 < tDen := by norm_num [tDen, B6402HybridP64.A, wY]
  have htDenQ : (0 : ℚ) < (tDen : ℚ) := by exact_mod_cast htDen
  have hM0Q : (0 : ℚ) < (w.M0 : ℚ) := by exact_mod_cast hM0pos
  have hFld : Fintype.card Fld = 2 ^ 192 := BF64.card_ext3
  have hFΦ' : 2 * B * W_Phi < Fintype.card Fld := by
    rw [hFld]; exact lt_trans hFΦ (by norm_num)
  have hFaux' : (4 * W_Phi / wY + B) * (4 * W_Phi) < Fintype.card Fld := by
    rw [hFld]; exact lt_trans hFaux (by norm_num)
  have hP0Z : 8 * (wY : ℤ) * w.slack * (w.h0 + 1 : ℤ) ^ 2 +
      16 * (wY : ℤ) * ((B6402HybridP64.A : ℤ) - wY + 10000) * (w.h0 + 1 : ℤ) + ((wY : ℤ) + 2) ^ 2 ≤
      64 * (wY : ℤ) * w.P0 * (w.h0 + 1 : ℤ) ^ 2 := by
    have hsub : ((B6402HybridP64.A - wY : ℕ) : ℤ) = (B6402HybridP64.A : ℤ) - wY := by norm_num [B6402HybridP64.A, wY]
    have hZ : ((8 * wY * w.slack * (w.h0 + 1) ^ 2 +
        16 * wY * (B6402HybridP64.A - wY + 10000) * (w.h0 + 1) + (wY + 2) ^ 2 : ℕ) : ℤ) ≤
        ((64 * wY * w.P0 * (w.h0 + 1) ^ 2 : ℕ) : ℤ) := by exact_mod_cast hP0
    push_cast [hsub] at hZ; exact hZ
  have hM0Z : (w.M0 : ℤ) + w.P0 = (B6402HybridP64.A : ℤ) - wY := by
    have hsub : ((B6402HybridP64.A - wY : ℕ) : ℤ) = (B6402HybridP64.A : ℤ) - wY := by norm_num [B6402HybridP64.A, wY]
    have hZ : ((w.M0 + w.P0 : ℕ) : ℤ) = ((B6402HybridP64.A - wY : ℕ) : ℤ) := by exact_mod_cast hM0eq
    push_cast [hsub] at hZ; exact hZ
  have hNeffZ : (N_eff : ℤ) = (B6402HybridP64.A : ℤ) - wY + DeltaMax := by
    dsimp only [N_eff]; push_cast [show ((B6402HybridP64.A - wY : ℕ) : ℤ) = (B6402HybridP64.A : ℤ) - wY by norm_num [B6402HybridP64.A, wY]]; rfl
  have hCd_arkQ : (2 * (w.h0 : ℚ) - 1) + (((N - wY : ℕ) : ℚ) / ((B6402HybridP64.A - wY : ℕ) : ℚ)) *
      (1 + (2 * (wY : ℚ) - 1) * (2 * (w.h0 : ℚ) - 1) + 2 * ((w.h0 - (2 * wY + 1) : ℕ) : ℚ)) ≤ (w.Cd : ℚ) := by
    have h2h : 1 ≤ 2 * w.h0 := by linarith
    have h2w : 1 ≤ 2 * wY := by norm_num [wY]
    have hQ : (((2 * w.h0 - 1) * tDen + tNum * (1 + (2 * wY - 1) * (2 * w.h0 - 1) + 2 * (w.h0 - (2 * wY + 1))) : ℕ) : ℚ) ≤
        (w.Cd : ℚ) * (tDen : ℚ) := by exact_mod_cast hCd_ark
    push_cast [Nat.cast_sub h2h, Nat.cast_sub h2w] at hQ
    change (2 * (w.h0 : ℚ) - 1) + ((tNum : ℚ) / (tDen : ℚ)) * _ ≤ (w.Cd : ℚ)
    have hne : (tDen : ℚ) ≠ 0 := htDenQ.ne'
    rw [show (2 * (w.h0 : ℚ) - 1) + ((tNum : ℚ) / (tDen : ℚ)) *
          (1 + (2 * (wY : ℚ) - 1) * (2 * (w.h0 : ℚ) - 1) + 2 * ((w.h0 - (2 * wY + 1) : ℕ) : ℚ)) =
        ((2 * (w.h0 : ℚ) - 1) * (tDen : ℚ) + (tNum : ℚ) *
          (1 + (2 * (wY : ℚ) - 1) * (2 * (w.h0 : ℚ) - 1) + 2 * ((w.h0 - (2 * wY + 1) : ℕ) : ℚ))) / (tDen : ℚ) by
      rw [add_div, mul_div_cancel_right₀ _ hne, mul_div_right_comm]]
    rw [div_le_iff₀ htDenQ]; linarith
  have hCd_c7Q : ((2 * N_eff * N * 6 : ℕ) : ℚ) / (w.M0 : ℚ) + (N : ℚ) ≤ (w.Cd : ℚ) := by
    have hQ : ((2 * N_eff * N * 6 + N * w.M0 : ℕ) : ℚ) ≤ (w.Cd : ℚ) * (w.M0 : ℚ) := by exact_mod_cast hCd_c7
    rw [show ((2 * N_eff * N * 6 : ℕ) : ℚ) / (w.M0 : ℚ) + (N : ℚ) =
        (((2 * N_eff * N * 6 : ℕ) : ℚ) + (N : ℚ) * (w.M0 : ℚ)) / (w.M0 : ℚ) by
      rw [add_div, mul_div_cancel_right₀ _ hM0Q.ne']]
    rw [div_le_iff₀ hM0Q]; push_cast at hQ ⊢; linarith
  have hCd_c6Q : ((16 * N_eff * N : ℕ) : ℚ) / (10000 ^ 2 : ℚ) + (N : ℚ) ≤ (w.Cd : ℚ) := by
    have hQ : ((16 * N_eff * N + N * 10000 ^ 2 : ℕ) : ℚ) ≤ (w.Cd : ℚ) * (10000 ^ 2 : ℚ) := by exact_mod_cast hCd_c6
    rw [show ((16 * N_eff * N : ℕ) : ℚ) / (10000 ^ 2 : ℚ) + (N : ℚ) =
        (((16 * N_eff * N : ℕ) : ℚ) + (N : ℚ) * (10000 ^ 2 : ℚ)) / (10000 ^ 2 : ℚ) by ring]
    rw [div_le_iff₀ (by norm_num)]; push_cast at hQ ⊢; linarith
  have hCh_lightQ : ((120000000000 : ℕ) : ℚ) / ((w.h0 + 1 : ℕ) : ℚ) ≤ (w.Ch : ℚ) := by
    rw [div_le_iff₀ (by positivity)]; exact_mod_cast hCh_light
  have hCh_arkQ : (q₀ : ℚ) * ((((N - wY : ℕ) : ℚ) / ((B6402HybridP64.A - wY : ℕ) : ℚ)) + ((N - wY - 1 : ℕ) : ℚ)) ≤ (w.Ch : ℚ) := by
    have hQ : ((q₀ * (tNum + (N - wY - 1) * tDen) : ℕ) : ℚ) ≤ (w.Ch : ℚ) * (tDen : ℚ) := by exact_mod_cast hCh_ark
    change (q₀ : ℚ) * (((tNum : ℚ) / (tDen : ℚ)) + ((N - wY - 1 : ℕ) : ℚ)) ≤ (w.Ch : ℚ)
    rw [show (q₀ : ℚ) * (((tNum : ℚ) / (tDen : ℚ)) + ((N - wY - 1 : ℕ) : ℚ)) =
        ((q₀ : ℚ) * ((tNum : ℚ) + ((N - wY - 1 : ℕ) : ℚ) * (tDen : ℚ))) / (tDen : ℚ) by field_simp [htDenQ.ne']]
    rw [div_le_iff₀ htDenQ]; push_cast at hQ; linarith
  have hCh_c7Q : ((2 * N_eff * N * (2 * q₀ + 2) : ℕ) : ℚ) / (w.M0 : ℚ) ≤ (w.Ch : ℚ) := by
    rw [div_le_iff₀ hM0Q]; exact_mod_cast hCh_c7
  have hCh_c6Q : ((2 * N_eff * (4 * q₀ + 1) : ℕ) : ℚ) / (10000 : ℚ) ≤ (w.Ch : ℚ) := by
    rw [div_le_iff₀ (by norm_num)]; exact_mod_cast hCh_c6
  have hp64 := hybrid_p64_card_le u₀ u₁ q₀ hq₀ Φ B H W_Phi m DeltaMax hΦ hB hH hWΦ hFΦ' hFaux'
    S P Az hP hcurve hcard hmatch hbad hΦgap
    20 30 496 120000000000 cert208984_6402 count208984_6402 (by norm_num)
    w.h0 w.q_aux w.slack w.P0 w.M0 N_eff hh0 hqaux hM0pos hBmul hC0h h4Bq hslack hP0Z hM0Z hNeffZ hMh
    (w.Cd : ℚ) (w.Ch : ℚ) hCd_arkQ (by exact_mod_cast hCd_light) hCd_c7Q hCd_c6Q
    (by exact_mod_cast hCh_aux) hCh_lightQ hCh_arkQ hCh_c7Q hCh_c6Q
  dsimp only at hp64
  have hrew' : (w.Cd : ℚ) * ((H : ℚ) + (q₀ : ℚ) * (B : ℚ)) +
      ((max (4 * W_Phi / wY : ℕ) (4 * B) : ℕ) + (B : ℚ)) * ((H : ℚ) + (q₀ : ℚ) * (B : ℚ)) +
      (w.Ch : ℚ) * (B : ℚ) + (H : ℚ) =
      (((w.Cd + M_B + B + 1 : ℕ) : ℚ) / (1 : ℕ)) * (H : ℚ) +
      ((((w.Cd + M_B + B) * q₀ * B + w.Ch * B : ℕ) : ℚ) / (1 : ℕ)) := by
    dsimp only [M_B, M_W]; push_cast; ring
  rw [hrew'] at hp64
  exact hp64

private lemma checkLinBridge
    (d m s W I0 rkSd δNum δDen q₀ D_ZF D_Z' c1Bkt c0Bkt kHNum kHDen k0Num k0Den : ℕ)
    (hm : 0 < m) (hδNum : 0 < δNum) (hδDen : 0 < δDen) (hkHD : 0 < kHDen) (hk0D : 0 < k0Den)
    (hDZ'_le : (D_Z' : ℚ) ≤ max ((D_ZF : ℚ) + (q₀ : ℚ) * ((W / wY : ℕ) : ℚ))
      ((((rkSd : ℚ) * (D_ZF : ℚ) +
          (q₀ : ℚ) * ((W / wY : ℕ) : ℚ) * (I0 : ℚ) / (N : ℚ)) /
        (((m : ℚ) * (m : ℚ)) * ((δNum : ℚ) / (δDen : ℚ)))) + 1))
    (h1a : kHNum * (d + s) ≤ c1Bkt * kHDen)
    (h1b : kHNum * (d * rkSd * δDen + s * m * m * δNum) ≤ c1Bkt * kHDen * m * m * δNum)
    (h2a : kHNum * (d * q₀ * (W / wY)) * k0Den + k0Num * kHDen ≤ c0Bkt * kHDen * k0Den)
    (h2b : kHNum * d * (q₀ * (W / wY) * I0 * δDen + N * m * m * δNum) * k0Den +
      k0Num * kHDen * N * m * m * δNum ≤ c0Bkt * kHDen * k0Den * N * m * m * δNum) :
    ((kHNum : ℚ) / (kHDen : ℚ)) * ((d * D_Z' + s * D_ZF : ℕ) : ℚ) + ((k0Num : ℚ) / (k0Den : ℚ)) ≤
      (c1Bkt : ℚ) * (D_ZF : ℚ) + (c0Bkt : ℚ) := by
  have hkHD_pos : (0 : ℚ) < kHDen := by exact_mod_cast hkHD
  have hk0D_pos : (0 : ℚ) < k0Den := by exact_mod_cast hk0D
  have hm2δ_pos : (0 : ℚ) < (m : ℚ) * (m : ℚ) * ((δNum : ℚ) / (δDen : ℚ)) := by
    have : (0 : ℚ) < m := by exact_mod_cast hm
    have : (0 : ℚ) < δNum := by exact_mod_cast hδNum
    have : (0 : ℚ) < δDen := by exact_mod_cast hδDen
    positivity
  have hN_pos : (0 : ℚ) < N := by norm_num [N]
  have h1aQ : ((kHNum : ℚ) / (kHDen : ℚ)) * ((d : ℚ) + (s : ℚ)) ≤ (c1Bkt : ℚ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hkHD_pos]; exact_mod_cast h1a
  have h1bQ : ((kHNum : ℚ) / (kHDen : ℚ)) *
      ((d : ℚ) * ((rkSd : ℚ) / ((m : ℚ) * (m : ℚ) * ((δNum : ℚ) / (δDen : ℚ)))) + (s : ℚ)) ≤ (c1Bkt : ℚ) := by
    have h1b' : (kHNum : ℚ) * ((d : ℚ) * (rkSd : ℚ) * (δDen : ℚ) + (s : ℚ) * (m : ℚ) * (m : ℚ) * (δNum : ℚ)) ≤
        (c1Bkt : ℚ) * (kHDen : ℚ) * (m : ℚ) * (m : ℚ) * (δNum : ℚ) := by exact_mod_cast h1b
    have hden_pos : (0 : ℚ) < (kHDen : ℚ) * ((m : ℚ) * (m : ℚ) * (δNum : ℚ)) := by
      have : (0 : ℚ) < m := by exact_mod_cast hm
      have : (0 : ℚ) < δNum := by exact_mod_cast hδNum
      positivity
    rw [show ((kHNum : ℚ) / (kHDen : ℚ)) *
          ((d : ℚ) * ((rkSd : ℚ) / ((m : ℚ) * (m : ℚ) * ((δNum : ℚ) / (δDen : ℚ)))) + (s : ℚ)) =
        ((kHNum : ℚ) * ((d : ℚ) * (rkSd : ℚ) * (δDen : ℚ) + (s : ℚ) * (m : ℚ) * (m : ℚ) * (δNum : ℚ))) /
          ((kHDen : ℚ) * ((m : ℚ) * (m : ℚ) * (δNum : ℚ))) by
          have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
          have : (δNum : ℚ) ≠ 0 := by exact_mod_cast hδNum.ne'
          have : (δDen : ℚ) ≠ 0 := by exact_mod_cast hδDen.ne'
          field_simp [hkHD_pos.ne']]
    rw [div_le_iff₀ hden_pos]; linarith
  have h2aQ : ((kHNum : ℚ) / (kHDen : ℚ)) * ((d : ℚ) * (q₀ : ℚ) * ((W / wY : ℕ) : ℚ)) +
      ((k0Num : ℚ) / (k0Den : ℚ)) ≤ (c0Bkt : ℚ) := by
    have h2a' : (kHNum : ℚ) * ((d : ℚ) * (q₀ : ℚ) * ((W / wY : ℕ) : ℚ)) * (k0Den : ℚ) +
        (k0Num : ℚ) * (kHDen : ℚ) ≤ (c0Bkt : ℚ) * (kHDen : ℚ) * (k0Den : ℚ) := by exact_mod_cast h2a
    have hden : (0 : ℚ) < (kHDen : ℚ) * (k0Den : ℚ) := by positivity
    rw [show ((kHNum : ℚ) / (kHDen : ℚ)) * ((d : ℚ) * (q₀ : ℚ) * ((W / wY : ℕ) : ℚ)) +
          ((k0Num : ℚ) / (k0Den : ℚ)) =
        ((kHNum : ℚ) * ((d : ℚ) * (q₀ : ℚ) * ((W / wY : ℕ) : ℚ)) * (k0Den : ℚ) +
          (k0Num : ℚ) * (kHDen : ℚ)) / ((kHDen : ℚ) * (k0Den : ℚ)) by field_simp [hkHD_pos.ne', hk0D_pos.ne']]
    rw [div_le_iff₀ hden]; linarith
  have h2bQ : ((kHNum : ℚ) / (kHDen : ℚ)) *
      ((d : ℚ) * (((q₀ : ℚ) * ((W / wY : ℕ) : ℚ) * (I0 : ℚ) / (N : ℚ)) /
          ((m : ℚ) * (m : ℚ) * ((δNum : ℚ) / (δDen : ℚ))) + 1)) +
      ((k0Num : ℚ) / (k0Den : ℚ)) ≤ (c0Bkt : ℚ) := by
    have h2b' : (kHNum : ℚ) * (d : ℚ) * ((q₀ : ℚ) * ((W / wY : ℕ) : ℚ) * (I0 : ℚ) * (δDen : ℚ) +
          (N : ℚ) * (m : ℚ) * (m : ℚ) * (δNum : ℚ)) * (k0Den : ℚ) +
        (k0Num : ℚ) * (kHDen : ℚ) * (N : ℚ) * (m : ℚ) * (m : ℚ) * (δNum : ℚ) ≤
        (c0Bkt : ℚ) * (kHDen : ℚ) * (k0Den : ℚ) * (N : ℚ) * (m : ℚ) * (m : ℚ) * (δNum : ℚ) := by
      exact_mod_cast h2b
    have hden : (0 : ℚ) < (kHDen : ℚ) * (k0Den : ℚ) * (N : ℚ) * (m : ℚ) * (m : ℚ) * (δNum : ℚ) := by
      have : (0 : ℚ) < m := by exact_mod_cast hm
      have : (0 : ℚ) < δNum := by exact_mod_cast hδNum
      positivity
    rw [show ((kHNum : ℚ) / (kHDen : ℚ)) *
          ((d : ℚ) * (((q₀ : ℚ) * ((W / wY : ℕ) : ℚ) * (I0 : ℚ) / (N : ℚ)) /
              ((m : ℚ) * (m : ℚ) * ((δNum : ℚ) / (δDen : ℚ))) + 1)) +
          ((k0Num : ℚ) / (k0Den : ℚ)) =
        ((kHNum : ℚ) * (d : ℚ) * ((q₀ : ℚ) * ((W / wY : ℕ) : ℚ) * (I0 : ℚ) * (δDen : ℚ) +
            (N : ℚ) * (m : ℚ) * (m : ℚ) * (δNum : ℚ)) * (k0Den : ℚ) +
          (k0Num : ℚ) * (kHDen : ℚ) * (N : ℚ) * (m : ℚ) * (m : ℚ) * (δNum : ℚ)) /
          ((kHDen : ℚ) * (k0Den : ℚ) * (N : ℚ) * (m : ℚ) * (m : ℚ) * (δNum : ℚ)) by
          have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
          have : (δNum : ℚ) ≠ 0 := by exact_mod_cast hδNum.ne'
          have : (δDen : ℚ) ≠ 0 := by exact_mod_cast hδDen.ne'
          field_simp [hkHD_pos.ne', hk0D_pos.ne', hN_pos.ne']]
    rw [div_le_iff₀ hden]; linarith
  have hkH_nn : (0 : ℚ) ≤ (kHNum : ℚ) / (kHDen : ℚ) := by positivity
  have hd_nn : (0 : ℚ) ≤ (d : ℚ) := by positivity
  have hDZF_nn : (0 : ℚ) ≤ (D_ZF : ℚ) := by positivity
  have hH_cast : ((d * D_Z' + s * D_ZF : ℕ) : ℚ) = (d : ℚ) * (D_Z' : ℚ) + (s : ℚ) * (D_ZF : ℚ) := by
    push_cast; rfl
  rcases le_max_iff.mp hDZ'_le with hA | hB'
  · have hH_le : ((d * D_Z' + s * D_ZF : ℕ) : ℚ) ≤ ((d : ℚ) + (s : ℚ)) * (D_ZF : ℚ) + (d : ℚ) * (q₀ : ℚ) * ((W / wY : ℕ) : ℚ) := by
      rw [hH_cast]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hH_le hkH_nn, mul_le_mul_of_nonneg_right h1aQ hDZF_nn]
  · have hsplit :
        (((rkSd : ℚ) * (D_ZF : ℚ) + (q₀ : ℚ) * ((W / wY : ℕ) : ℚ) * (I0 : ℚ) / (N : ℚ)) /
          (((m : ℚ) * (m : ℚ)) * ((δNum : ℚ) / (δDen : ℚ)))) + 1 =
        ((rkSd : ℚ) / (((m : ℚ) * (m : ℚ)) * ((δNum : ℚ) / (δDen : ℚ)))) * (D_ZF : ℚ) +
        (((q₀ : ℚ) * ((W / wY : ℕ) : ℚ) * (I0 : ℚ) / (N : ℚ)) /
          (((m : ℚ) * (m : ℚ)) * ((δNum : ℚ) / (δDen : ℚ))) + 1) := by
      rw [add_div, mul_div_right_comm]; ring
    rw [hsplit] at hB'
    have hH_le : ((d * D_Z' + s * D_ZF : ℕ) : ℚ) ≤
        ((d : ℚ) * ((rkSd : ℚ) / (((m : ℚ) * (m : ℚ)) * ((δNum : ℚ) / (δDen : ℚ)))) + (s : ℚ)) * (D_ZF : ℚ) +
        (d : ℚ) * (((q₀ : ℚ) * ((W / wY : ℕ) : ℚ) * (I0 : ℚ) / (N : ℚ)) /
          (((m : ℚ) * (m : ℚ)) * ((δNum : ℚ) / (δDen : ℚ))) + 1) := by
      rw [hH_cast]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hH_le hkH_nn, mul_le_mul_of_nonneg_right h1bQ hDZF_nn]

private lemma arklib_alg (B H q₀ tNum tDen psi c0 : ℚ) (htDen : tDen ≠ 0) :
    (2 * B - 1) * H + (tNum / tDen) * (q₀ * B + H * psi) + q₀ * c0 * B =
    (((2 * B - 1) * tDen + tNum * psi) / tDen) * H +
    ((tNum * q₀ * B + q₀ * c0 * B * tDen) / tDen) := by
  field_simp [htDen]; ring

private lemma arklib_eq_ratio (wY_ N_ A_ B H q₀ : ℕ)
    (hB1 : 1 ≤ B) (h2wY1 : 1 ≤ 2 * wY_) (htDen : 0 < A_ - wY_) :
    let tNum : ℕ := N_ - wY_
    let tDen : ℕ := A_ - wY_
    let psi : ℕ := 1 + (2 * wY_ - 1) * (2 * B - 1) + 2 * (B - (2 * wY_ + 1))
    let kHNum : ℕ := (2 * B - 1) * tDen + tNum * psi
    let k0Num : ℕ := tNum * q₀ * B + q₀ * (N_ - wY_ - 1) * B * tDen
    (2 * (B : ℚ) - 1) * (H : ℚ) +
      (((tNum : ℕ) : ℚ) / ((tDen : ℕ) : ℚ)) * ((q₀ : ℚ) * (B : ℚ) + (H : ℚ) *
        (1 + (2 * (wY_ : ℚ) - 1) * (2 * (B : ℚ) - 1) + 2 * ((B - (2 * wY_ + 1) : ℕ) : ℚ))) +
      (q₀ : ℚ) * ((N_ - wY_ - 1 : ℕ) : ℚ) * (B : ℚ) =
    (((kHNum : ℕ) : ℚ) / (tDen : ℚ)) * (H : ℚ) + (((k0Num : ℕ) : ℚ) / (tDen : ℚ)) := by
  intro tNum tDen psi kHNum k0Num
  have htDenQ : (0 : ℚ) < (tDen : ℚ) := by exact_mod_cast htDen
  have h2B1 : 1 ≤ 2 * B := by omega
  have hpsiQ : 1 + (2 * (wY_ : ℚ) - 1) * (2 * (B : ℚ) - 1) + 2 * ((B - (2 * wY_ + 1) : ℕ) : ℚ) = (psi : ℚ) := by
    dsimp only [psi]
    push_cast [Nat.cast_sub h2wY1, Nat.cast_sub h2B1]
    ring
  have hkH_cast : (kHNum : ℚ) = (2 * (B : ℚ) - 1) * (tDen : ℚ) + (tNum : ℚ) * (psi : ℚ) := by
    dsimp only [kHNum]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h2B1, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hk0_cast : (k0Num : ℚ) =
      (tNum : ℚ) * (q₀ : ℚ) * (B : ℚ) + (q₀ : ℚ) * ((N_ - wY_ - 1 : ℕ) : ℚ) * (B : ℚ) * (tDen : ℚ) := by
    dsimp only [k0Num]
    simp only [Nat.cast_add, Nat.cast_mul]
  rw [hpsiQ, hkH_cast, hk0_cast]
  exact arklib_alg (B : ℚ) (H : ℚ) (q₀ : ℚ) (tNum : ℚ) (tDen : ℚ) (psi : ℚ) ((N_ - wY_ - 1 : ℕ) : ℚ) htDenQ.ne'

private lemma arklib_H_le_ratio (wY_ N_ A_ B H q₀ : ℕ)
    (hB1 : 1 ≤ B) (htDen : 0 < A_ - wY_) :
    let tNum : ℕ := N_ - wY_
    let tDen : ℕ := A_ - wY_
    let psi : ℕ := 1 + (2 * wY_ - 1) * (2 * B - 1) + 2 * (B - (2 * wY_ + 1))
    let kHNum : ℕ := (2 * B - 1) * tDen + tNum * psi
    let k0Num : ℕ := tNum * q₀ * B + q₀ * (N_ - wY_ - 1) * B * tDen
    (H : ℚ) ≤ (((kHNum : ℕ) : ℚ) / (tDen : ℚ)) * (H : ℚ) + (((k0Num : ℕ) : ℚ) / (tDen : ℚ)) := by
  intro tNum tDen psi kHNum k0Num
  have htDenQ : (0 : ℚ) < (tDen : ℚ) := by exact_mod_cast htDen
  have h1 : (1 : ℚ) ≤ ((kHNum : ℕ) : ℚ) / (tDen : ℚ) := by
    rw [le_div_iff₀ htDenQ, one_mul]
    have h2B_ge : 1 ≤ 2 * B - 1 := by omega
    have : tDen ≤ kHNum := Nat.le_trans (Nat.le_mul_of_pos_left tDen h2B_ge) (Nat.le_add_right _ _)
    exact_mod_cast this
  have h2 : (0 : ℚ) ≤ ((k0Num : ℕ) : ℚ) / (tDen : ℚ) := by positivity
  have hH0 : (0 : ℚ) ≤ (H : ℚ) := by positivity
  calc (H : ℚ) = 1 * (H : ℚ) + 0 := by ring
    _ ≤ (((kHNum : ℕ) : ℚ) / (tDen : ℚ)) * (H : ℚ) + (((k0Num : ℕ) : ℚ) / (tDen : ℚ)) :=
      add_le_add (mul_le_mul_of_nonneg_right h1 hH0) h2

private lemma checkArklib_card_le
    (u₀ u₁ : Idx → Fld) (B H q₀ : ℕ) (hq₀pos : 1 ≤ q₀) (hB1 : 1 ≤ B)
    (Φ : Polynomial (Polynomial (Polynomial Fld)))
    (hΦ : Φ ≠ 0) (hB : Φ.natDegree ≤ B) (hH : ∀ j a, ((Φ.coeff j).coeff a).natDegree ≤ H)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval Φ z (P z) = 0)
    (hcard : ∀ z ∈ S, B6402HybridP64.A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6402 u₀ u₁ (Az z)) :
    let tNum : ℕ := N - wY
    let tDen : ℕ := B6402HybridP64.A - wY
    let psi : ℕ := 1 + (2 * wY - 1) * (2 * B - 1) + 2 * (B - (2 * wY + 1))
    let kHNum : ℕ := (2 * B - 1) * tDen + tNum * psi
    let k0Num : ℕ := tNum * q₀ * B + q₀ * (N - wY - 1) * B * tDen
    (S.card : ℚ) ≤ (((kHNum : ℕ) : ℚ) / (tDen : ℚ)) * (H : ℚ) + (((k0Num : ℕ) : ℚ) / (tDen : ℚ)) := by
  have hark := card_le_of_biPoly_pow u₀ u₁ q₀ hq₀pos Φ B H hΦ hB hH S P Az
    hP hcurve hcard (fun z hz i hi => (hmatch z hz i).mp hi) hbad
  have htDen : 0 < B6402HybridP64.A - wY := by norm_num [B6402HybridP64.A, wY]
  have h2wY1 : 1 ≤ 2 * wY := by norm_num [wY]
  have hark_eq : arklibBoundPowQ q₀ B H = _ := arklib_eq_ratio wY N B6402HybridP64.A B H q₀ hB1 h2wY1 htDen
  rw [hark_eq] at hark
  exact hark.trans (max_le (arklib_H_le_ratio wY N B6402HybridP64.A B H q₀ hB1 htDen) le_rfl)

/-- **Soundness of `checkCapWitness` (ArkLib or Hybrid-P64):**
Whenever `checkCapWitness ... w = true`, for ANY `D_ZF : ℕ` and `D_Z' = max (D_ZF + q₀*(W/wY))
(⌊(rk(m,s-d)*D_ZF + q₀*(W/wY)*I0/N) / (m^2 * δ)⌋ + 1)` and `H = d * D_Z' + s * D_ZF`,
every nonzero `Φ : Tri` of `deg_Y ≤ B`, `deg_Z ≤ H`, `wd Φ wY ≤ W_Phi` (with `hΦgap` when `useP64 = true`)
has `(S.card : ℚ) ≤ w.c1Bkt * D_ZF + w.c0Bkt`! -/
theorem checkCapWitness_sound
    (u₀ u₁ : Idx → Fld) (d m s cHiNum cHiDen δNum δDen hiGNum hiGDen q₀ D_ZF D_Z' : ℕ)
    (w : CapWitness)
    (hchk : checkCapWitness d m s cHiNum cHiDen δNum δDen hiGNum hiGDen q₀ w = true)
    (hq₀ : q₀ = 1 ∨ q₀ = 2)
    (hDZ'_le : (D_Z' : ℚ) ≤ max ((D_ZF : ℚ) + (q₀ : ℚ) * (((2 * B6402HybridP64.A * m - 1) / wY : ℕ) : ℚ))
      ((((rankKerD m (s - d) : ℚ) * (D_ZF : ℚ) +
          (q₀ : ℚ) * (((2 * B6402HybridP64.A * m - 1) / wY : ℕ) : ℚ) *
            ((varsKerDExact wY (2 * B6402HybridP64.A * m - 1) s -
              varsKerDExact wY ((2 * B6402HybridP64.A * m - 1) - ceilDivNat (cHiNum * wY) cHiDen) (s - d) : ℕ) : ℚ) / (N : ℚ)) /
        (((m : ℚ) * (m : ℚ)) * ((δNum : ℚ) / (δDen : ℚ)))) + 1))
    (Φ : Polynomial (Polynomial (Polynomial Fld)))
    (hΦ : Φ ≠ 0)
    (hWΦ : P64Caps.Weighted.weightedSupportDegree Φ wY ≤
      d * (2 * B6402HybridP64.A * m - 1) + s * (ceilDivNat (cHiNum * wY) cHiDen - d * (wY - 1)))
    (hB : Φ.natDegree ≤ (d * (2 * B6402HybridP64.A * m - 1) + s * (ceilDivNat (cHiNum * wY) cHiDen - d * (wY - 1))) / wY)
    (hH : ∀ j a, ((Φ.coeff j).coeff a).natDegree ≤ d * D_Z' + s * D_ZF)
    (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ wY)
    (hcurve : ∀ z ∈ S, triEval Φ z (P z) = 0)
    (hcard : ∀ z ∈ S, B6402HybridP64.A ≤ (Az z).card)
    (hmatch : ∀ z ∈ S, ∀ i, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z ^ q₀ * u₁ i)
    (hbad : ∀ z ∈ S, BadOn6402 u₀ u₁ (Az z))
    (hΦgap : w.useP64 = true → ∀ z ∈ S,
      (P64Caps.Weighted.weightedSupportDegree Φ wY : ℤ) -
        (∑ i ∈ Az z, (P64LineOrder.lineOrd Φ (BinaryIRSProfile.domain i) (linePow u₀ u₁ q₀ i) : ℤ)) +
        (2 * m : ℤ) * ((Az z).card - (B6402HybridP64.A : ℤ)) ≤ ((s * hiGNum * N) / hiGDen : ℕ)) :
    (S.card : ℚ) ≤ (w.c1Bkt : ℚ) * (D_ZF : ℚ) + (w.c0Bkt : ℚ) := by
  unfold checkCapWitness at hchk
  have hbadp : ¬ (m = 0 ∨ s < d ∨ cHiDen = 0 ∨ δNum = 0 ∨ δDen = 0 ∨ hiGDen = 0) := by
    intro hbad
    have htrue : (m == 0 || s < d || cHiDen == 0 || δNum == 0 || δDen == 0 || hiGDen == 0) = true := by
      rcases hbad with rfl | h | rfl | rfl | rfl | rfl <;> simp_all
    simp [htrue] at hchk
  have hfalse : (m == 0 || s < d || cHiDen == 0 || δNum == 0 || δDen == 0 || hiGDen == 0) = false := by
    push Not at hbadp
    rcases hbadp with ⟨h1, h2, h3, h4, h5, h6⟩
    simp [h1, Nat.not_lt.mpr h2, h3, h4, h5, h6]
  rw [hfalse, ite_eq_right Bool.false_ne_true] at hchk
  push Not at hbadp
  have hm : 0 < m := Nat.pos_of_ne_zero hbadp.1
  have hδNum : 0 < δNum := Nat.pos_of_ne_zero hbadp.2.2.2.1
  have hδDen : 0 < δDen := Nat.pos_of_ne_zero hbadp.2.2.2.2.1
  have hq₀pos : 1 ≤ q₀ := by rcases hq₀ with rfl | rfl <;> omega
  cases huse : w.useP64
  · simp only [huse, Bool.not_false, eq_self, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨hB1, hlin_chk⟩
    obtain ⟨h1a, h1b, h2a, h2b⟩ := checkLinearCap_mp hlin_chk
    have hark := checkArklib_card_le u₀ u₁ _ (d * D_Z' + s * D_ZF) q₀ hq₀pos hB1 Φ hΦ hB hH
      S P Az hP hcurve hcard hmatch hbad
    have htDen : 0 < B6402HybridP64.A - wY := by norm_num [B6402HybridP64.A, wY]
    exact hark.trans (checkLinBridge d m s _ _ _ δNum δDen q₀ D_ZF D_Z' w.c1Bkt w.c0Bkt _ _ _ _
      hm hδNum hδDen htDen htDen hDZ'_le h1a h1b h2a h2b)
  · simp only [huse, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hchk
    rcases hchk with ⟨hside_chk, hlin_chk⟩
    obtain ⟨h1a, h1b, h2a, h2b⟩ := checkLinearCap_mp hlin_chk
    have hp64 := checkSideP64_card_le u₀ u₁ d m _ (d * D_Z' + s * D_ZF) _ ((s * hiGNum * N) / hiGDen) q₀ w hq₀
      hside_chk Φ hΦ hWΦ hB hH S P Az hP hcurve hcard hmatch hbad (hΦgap huse)
    exact hp64.trans (checkLinBridge d m s _ _ _ δNum δDen q₀ D_ZF D_Z' w.c1Bkt w.c0Bkt _ 1 _ 1
      hm hδNum hδDen (by norm_num) (by norm_num) hDZ'_le h1a h1b h2a h2b)

/-! ### Part 3: Universal Sparse-`Int` Table 4 Farkas Verifier & Soundness Theorem -/

/-- Exact static scale denominator `BASE_DEN = 4 * N = 8,388,608` (clears ALL denominators in ALL Table 4 rows!). -/
def BASE_DEN : ℤ := 4 * (N : ℤ)

/-- One sparse inequality or equality row: `∑ (j, a_j) * x_j ≤ rhsNum / rhsDen` (with LHS entries scaled by `BASE_DEN`!). -/
structure SparseRow where
  entries : List (Nat × Int)
  rhsNum : Int
  rhsDen : Int
  deriving Repr

/-- Exact sparse Table 4 bucket certificate (either `m = 0` infeasibility, or single `(m, s)` + exact `CapWitness`!). -/
structure T4BucketCert where
  loGNum : Nat
  loGDen : Nat
  hiGNum : Nat
  hiGDen : Nat
  m : Nat
  s : Nat
  scaleS : Int
  yMults : List (Nat × Int) -- (rowIdx, Y_r ≥ 0)
  zMults : List (Nat × Int) -- (eqIdx, Z_e)
  δNum : Nat
  δDen : Nat           -- claimed exact surplus lower bound (ignored when m == 0)
  cap1 : CapWitness         -- exact affine cap witness for q₀ = 1
  cap2 : CapWitness         -- exact affine cap witness for q₀ = 2
  deriving Repr

/-- Accumulate sparse dual column vector `∑ Y_r * A_ub[r] + ∑ Z_e * A_eq[e]` into an `Array Int` of length `nv`! -/
def accumDualCols (nv : Nat) (ubRows eqRows : Array SparseRow)
    (yMults zMults : List (Nat × Int)) : Array Int :=
  let a1 := yMults.foldl (fun acc (r, yr) =>
    if hr : r < ubRows.size then
      (ubRows[r]).entries.foldl (fun a (j, coeff) =>
        if hj : j < a.size then a.set j (a[j] + yr * coeff) else a) acc
    else acc) (Array.replicate nv (0 : Int))
  zMults.foldl (fun acc (e, ze) =>
    if he : e < eqRows.size then
      (eqRows[e]).entries.foldl (fun a (j, coeff) =>
        if hj : j < a.size then a.set j (a[j] + ze * coeff) else a) acc
    else acc) a1

/-- Exact rational sum `∑_r Y_r * (rhsNum_r / rhsDen_r) + ∑_e Z_e * (rhsNum_e / rhsDen_e)`
returned as `(num, den)` with `den > 0`, grouping terms sharing the SAME denominator first so
denominators stay tiny (at most `BASE_DEN * cLoDen * cHiDen * 1000`)! -/
def addFracPair (a b : Int × Int) : Int × Int :=
  if a.2 == b.2 then (a.1 + b.1, a.2)
  else if a.1 == 0 then b
  else if b.1 == 0 then a
  else (a.1 * b.2 + b.1 * a.2, a.2 * b.2)

def dualRhsFrac (ubRows eqRows : Array SparseRow) (yMults zMults : List (Nat × Int)) : Int × Int :=
  let s1 := yMults.foldl (fun acc (r, yr) =>
    if hr : r < ubRows.size then
      let row := ubRows[r]
      addFracPair acc (yr * row.rhsNum, row.rhsDen)
    else acc) (0, BASE_DEN)
  zMults.foldl (fun acc (e, ze) =>
    if he : e < eqRows.size then
      let row := eqRows[e]
      addFracPair acc (ze * row.rhsNum, row.rhsDen)
    else acc) s1

/-- **Pure-`Int` Table 4 single-bucket Farkas + Cap checker** (ZERO `Rat`, ZERO `Nat.gcd`!):
Checks:
1. All `yMults` have `yr ≥ 0`, `scaleS > 0`, all row indices in bounds;
2. Dual column feasibility on ALL `nv` columns (`j = 0..nv-1`):
   - `j ∈ 0..3`: `acc[j] * m^2 ≥ BASE_DEN * scaleS * (rk(m, s) - rk(m - j, s - 1))`
   - `j = 4`: `acc[4] * m^2 ≥ BASE_DEN * scaleS * (rk_3 - rk_2)`
   - `j = ic` (`nv - 1`): `acc[ic] / BASE_DEN + scaleS * v_sl ≥ 0` (exact `Int` cross-mult!)
   - all other `j`: `acc[j] ≥ 0`!
3. Objective bound:
   - if `m == 0`: `rhsNum < 0` (infeasibility contradiction!);
   - if `m > 0`: `v_lo - v_sl * c_lo - rhs / scaleS > δNum / δDen`, AND BOTH `cap1` (`q₀ = 1`) and `cap2` (`q₀ = 2`) pass `checkCapWitness`! -/
def checkT4Bucket (nv : Nat) (ubRows eqRows : Array SparseRow)
    (cLoNum cLoDen cHiNum cHiDen : Nat) (b : T4BucketCert) : Bool :=
  let ic := nv - 1
  if nv < 6 || cLoDen == 0 || cHiDen == 0 || b.scaleS ≤ 0 then false
  else if !b.yMults.all (fun (r, yr) => r < ubRows.size && 0 ≤ yr) then false
  else if !b.zMults.all (fun (e, _) => e < eqRows.size) then false
  else if !((cLoNum : ℤ) * cHiDen < (cHiNum : ℤ) * cLoDen) then false
  else
    let cols := accumDualCols nv ubRows eqRows b.yMults b.zMults
    let (rhsN, rhsD) := dualRhsFrac ubRows eqRows b.yMults b.zMults
    if rhsD ≤ 0 then false
    else if b.m == 0 then
      -- Pure infeasibility: all columns ≥ 0 and rhsN < 0!
      cols.toList.all (fun v => 0 ≤ v) && (rhsN < 0)
    else
      let m := b.m; let s := b.s
      if s < 1 || b.δNum == 0 || b.δDen == 0 then false
      else
        let rk (k : Nat) : Int := (rankKerD m s - rankKerD (m - k) (s - 1) : Int)
        let rks : Array Int := #[rk 0, rk 1, rk 2, rk 3, rk 3 - rk 2]
        let m2 : Int := (m : Int) * (m : Int)
        let colsBasicOk : Bool :=
          (List.range nv).all fun j =>
            if h : j < cols.size then
              let cj := cols[j]
              if j < 5 then
                BASE_DEN * b.scaleS * rks[j]! ≤ cj * m2
              else if j == ic then true
              else 0 ≤ cj
            else false
        -- Compute exact v_lo = vLoN / vLoD, v_hi = vHiN / vHiD, v_sl = (v_hi - v_lo) / (c_hi - c_lo):
        let vLoN := vquotNum 1 m s cLoNum cLoDen
        let vLoD := vquotDen m cLoDen
        let vHiN := vquotNum 1 m s cHiNum cHiDen
        let vHiD := vquotDen m cHiDen
        -- v_hi - v_lo = (vHiN * vLoD - vLoN * vHiD) / (vLoD * vHiD)
        -- c_hi - c_lo = (cHiNum * cLoDen - cLoNum * cHiDen) / (cLoDen * cHiDen)
        -- So v_sl = slNum / slDen where:
        let slNum : Int := (vHiN * vLoD - vLoN * vHiD) * ((cLoDen : Int) * (cHiDen : Int))
        let slDen : Int := (vLoD * vHiD) * ((cHiNum : Int) * (cLoDen : Int) - (cLoNum : Int) * (cHiDen : Int))
        -- Column ic check: cols[ic] / BASE_DEN + scaleS * slNum / slDen ≥ 0
        let colIcOk : Bool :=
          if hic : ic < cols.size then
            0 ≤ cols[ic] * slDen + BASE_DEN * b.scaleS * slNum
          else false
        -- Objective check: vLoN/vLoD - (slNum/slDen)*(cLoNum/cLoDen) - rhsN/(scaleS*rhsD) > δNum/δDen!
        -- Notice vLoN/vLoD - (slNum/slDen)*(cLoNum/cLoDen) = v0Num / v0Den where:
        let v0Num : Int := vLoN * slDen * (cLoDen : Int) - slNum * (cLoNum : Int) * vLoD
        let v0Den : Int := vLoD * slDen * (cLoDen : Int)
        let objOk : Bool :=
          (b.δNum : Int) * v0Den * b.scaleS * rhsD <
            (v0Num * b.scaleS * rhsD - rhsN * v0Den) * (b.δDen : Int)
        let cap1Ok := checkCapWitness 1 m s cHiNum cHiDen b.δNum b.δDen b.hiGNum b.hiGDen 1 b.cap1
        let cap2Ok := checkCapWitness 1 m s cHiNum cHiDen b.δNum b.δDen b.hiGNum b.hiGDen 2 b.cap2
        colsBasicOk && colIcOk && objOk && cap1Ok && cap2Ok

/-- **Universal soundness theorem for `checkT4Bucket`:**
For ANY primal point `x : Fin nv → ℚ` (`x ≥ 0`) satisfying:
- every `r < ubRows.size`: `∑ (j, a) ∈ ubRows[r].entries, (a / BASE_DEN) * x j ≤ rhsNum / rhsDen`,
- every `e < eqRows.size`: `∑ (j, a) ∈ eqRows[e].entries, (a / BASE_DEN) * x j = rhsNum / rhsDen`,
if `checkT4Bucket nv ubRows eqRows cLoNum cLoDen cHiNum cHiDen b = true`, then:
- if `b.m = 0`: `False` (contradiction!);
- if `b.m > 0`: `δNum / δDen < vquotLbQ 1 m s (x ic) - (∑_{k<4} rks[k]*x_k + (rk3 - rk2)*x_4)`
  (provided `cLo ≤ x ic ≤ cHi`), AND both `cap1` and `cap2` pass `checkCapWitness`! -/
private lemma addFracPair_val (a b : Int × Int) (ha : 0 < a.2) (hb : 0 < b.2) :
    0 < (addFracPair a b).2 ∧
    ((addFracPair a b).1 : ℚ) / ((addFracPair a b).2 : ℚ) =
      (a.1 : ℚ) / (a.2 : ℚ) + (b.1 : ℚ) / (b.2 : ℚ) := by
  unfold addFracPair
  split_ifs with h1 h2 h3
  · have heq : a.2 = b.2 := eq_of_beq h1
    refine ⟨ha, ?_⟩
    rw [heq]; push_cast; ring
  · have h0 : a.1 = 0 := eq_of_beq h2
    refine ⟨hb, ?_⟩; simp [h0]
  · have h0 : b.1 = 0 := eq_of_beq h3
    refine ⟨ha, ?_⟩; simp [h0]
  · refine ⟨mul_pos ha hb, ?_⟩
    have haQ : (a.2 : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have hbQ : (b.2 : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast; field_simp [haQ, hbQ]

private lemma dualRhsFrac_val (ubRows eqRows : Array SparseRow)
    (yMults zMults : List (Nat × Int))
    (hy : ∀ p ∈ yMults, p.1 < ubRows.size)
    (hz : ∀ p ∈ zMults, p.1 < eqRows.size)
    (hubD : ∀ i (hi : i < ubRows.size), 0 < (ubRows[i]).rhsDen)
    (heqD : ∀ i (hi : i < eqRows.size), 0 < (eqRows[i]).rhsDen) :
    0 < (dualRhsFrac ubRows eqRows yMults zMults).2 ∧
    ((dualRhsFrac ubRows eqRows yMults zMults).1 : ℚ) / ((dualRhsFrac ubRows eqRows yMults zMults).2 : ℚ) =
      (yMults.map fun p =>
        if h : p.1 < ubRows.size then (p.2 : ℚ) * ((ubRows[p.1]).rhsNum : ℚ) / ((ubRows[p.1]).rhsDen : ℚ)
        else 0).sum +
      (zMults.map fun p =>
        if h : p.1 < eqRows.size then (p.2 : ℚ) * ((eqRows[p.1]).rhsNum : ℚ) / ((eqRows[p.1]).rhsDen : ℚ)
        else 0).sum := by
  have hfold_frac : ∀ (rows : Array SparseRow) (ms : List (Nat × Int)) (init : Int × Int),
      0 < init.2 → (∀ p ∈ ms, p.1 < rows.size) → (∀ i (hi : i < rows.size), 0 < (rows[i]).rhsDen) →
      let res := ms.foldl (fun acc (r, yr) =>
        if hr : r < rows.size then addFracPair acc (yr * (rows[r]).rhsNum, (rows[r]).rhsDen) else acc) init
      0 < res.2 ∧ (res.1 : ℚ) / (res.2 : ℚ) =
        (init.1 : ℚ) / (init.2 : ℚ) +
        (ms.map fun p =>
          if h : p.1 < rows.size then (p.2 : ℚ) * ((rows[p.1]).rhsNum : ℚ) / ((rows[p.1]).rhsDen : ℚ)
          else 0).sum := by
    intro rows ms
    induction ms with
    | nil => intro init hi _ _; simp [hi]
    | cons p tl ih =>
        intro init hi hms hD
        have hp : p.1 < rows.size := hms p (by simp)
        have hstep := addFracPair_val init (p.2 * (rows[p.1]).rhsNum, (rows[p.1]).rhsDen) hi (hD p.1 hp)
        have hrec := ih (addFracPair init (p.2 * (rows[p.1]).rhsNum, (rows[p.1]).rhsDen)) hstep.1
          (fun q hq => hms q (by simp [hq])) hD
        simp only [List.foldl_cons, hp, ↓reduceDIte, List.map_cons, List.sum_cons]
        refine ⟨hrec.1, ?_⟩
        rw [hrec.2, hstep.2]
        push_cast; ring
  have hBpos : (0 : ℤ) < BASE_DEN := by norm_num [BASE_DEN, N]
  have h1 := hfold_frac ubRows yMults (0, BASE_DEN) hBpos hy hubD
  have h2 := hfold_frac eqRows zMults _ h1.1 hz heqD
  unfold dualRhsFrac
  refine ⟨h2.1, ?_⟩
  rw [h2.2, h1.2]
  simp

private lemma accumDualCols_dot {nv : Nat} (ubRows eqRows : Array SparseRow)
    (yMults zMults : List (Nat × Int)) (x : Fin nv → ℚ)
    (hy : ∀ p ∈ yMults, p.1 < ubRows.size)
    (hz : ∀ p ∈ zMults, p.1 < eqRows.size)
    (hub_entries : ∀ i (hi : i < ubRows.size), ∀ e ∈ (ubRows[i]).entries, e.1 < nv)
    (heq_entries : ∀ i (hi : i < eqRows.size), ∀ e ∈ (eqRows[i]).entries, e.1 < nv) :
    let cols := accumDualCols nv ubRows eqRows yMults zMults
    ∃ hsz : cols.size = nv,
    (∑ j : Fin nv, (cols[j.val]'(by omega) : ℚ) * x j) =
      (yMults.map fun p =>
        if h : p.1 < ubRows.size then
          (p.2 : ℚ) * ((ubRows[p.1]).entries.map fun e =>
            if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum
        else 0).sum +
      (zMults.map fun p =>
        if h : p.1 < eqRows.size then
          (p.2 : ℚ) * ((eqRows[p.1]).entries.map fun e =>
            if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum
        else 0).sum := by
  -- Helper: adding one sparse entry list multiplies dot product by yr * (entries · x)!
  have hadd_entries : ∀ (entries : List (Nat × Int)) (yr : Int) (acc : Array Int) (hsz : acc.size = nv),
      (∀ e ∈ entries, e.1 < nv) →
      let out := entries.foldl (fun a (j, coeff) =>
        if hj : j < a.size then a.set j (a[j] + yr * coeff) else a) acc
      ∃ hout : out.size = nv,
      (∑ j : Fin nv, (out[j.val]'(by omega) : ℚ) * x j) =
        (∑ j : Fin nv, (acc[j.val]'(by omega) : ℚ) * x j) +
        (yr : ℚ) * (entries.map fun e => if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum := by
    intro entries yr
    induction entries with
    | nil => intro acc hsz _; exact ⟨hsz, by simp⟩
    | cons e tl ih =>
        intro acc hsz hent
        have he_lt : e.1 < nv := hent e (by simp)
        have he_acc : e.1 < acc.size := by omega
        let acc' := acc.set e.1 (acc[e.1]'he_acc + yr * e.2)
        have hsz' : acc'.size = nv := by simp [acc', hsz]
        obtain ⟨hrec_sz, hrec_eq⟩ := ih acc' hsz' (fun e' he' => hent e' (by simp [he']))
        simp only [List.foldl_cons, he_acc, ↓reduceDIte, List.map_cons, List.sum_cons, he_lt]
        refine ⟨hrec_sz, ?_⟩
        rw [hrec_eq]
        have hstep : (∑ j : Fin nv, (acc'[j.val]'(by omega) : ℚ) * x j) =
            (∑ j : Fin nv, (acc[j.val]'(by omega) : ℚ) * x j) + (yr : ℚ) * ((e.2 : ℚ) * x ⟨e.1, he_lt⟩) := by
          have hpt : ∀ j : Fin nv, (acc'[j.val]'(by omega) : ℚ) * x j =
              (acc[j.val]'(by omega) : ℚ) * x j +
                if j = ⟨e.1, he_lt⟩ then (yr : ℚ) * ((e.2 : ℚ) * x ⟨e.1, he_lt⟩) else 0 := by
            intro j
            dsimp only [acc']
            by_cases hje : j.val = e.1
            · have hje' : j = ⟨e.1, he_lt⟩ := Fin.ext hje
              subst hje'
              simp only [Array.getElem_set_self, Int.cast_add, Int.cast_mul, ↓reduceIte]
              ring
            · have hje' : j ≠ ⟨e.1, he_lt⟩ := fun h => hje (congrArg Fin.val h)
              have hne : e.1 ≠ j.val := Ne.symm hje
              have hj_acc : j.val < acc.size := by omega
              rw [Array.getElem_set_ne (pj := hj_acc) (h := hne)]
              simp [hje']
          simp_rw [hpt]
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp
        rw [hstep]; ring
  have hadd_rows : ∀ (rows : Array SparseRow) (ms : List (Nat × Int)) (acc : Array Int) (hsz : acc.size = nv),
      (∀ p ∈ ms, p.1 < rows.size) →
      (∀ i (hi : i < rows.size), ∀ e ∈ (rows[i]).entries, e.1 < nv) →
      let out := ms.foldl (fun acc (r, yr) =>
        if hr : r < rows.size then
          (rows[r]).entries.foldl (fun a (j, coeff) =>
            if hj : j < a.size then a.set j (a[j] + yr * coeff) else a) acc
        else acc) acc
      ∃ hout : out.size = nv,
      (∑ j : Fin nv, (out[j.val]'(by omega) : ℚ) * x j) =
        (∑ j : Fin nv, (acc[j.val]'(by omega) : ℚ) * x j) +
        (ms.map fun p =>
          if h : p.1 < rows.size then
            (p.2 : ℚ) * ((rows[p.1]).entries.map fun e =>
              if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum
          else 0).sum := by
    intro rows ms
    induction ms with
    | nil => intro acc hsz _ _; exact ⟨hsz, by simp⟩
    | cons p tl ih =>
        intro acc hsz hms hent
        have hp : p.1 < rows.size := hms p (by simp)
        obtain ⟨hs_sz, hs_eq⟩ := hadd_entries (rows[p.1]).entries p.2 acc hsz (hent p.1 hp)
        obtain ⟨hr_sz, hr_eq⟩ := ih _ hs_sz (fun q hq => hms q (by simp [hq])) hent
        simp only [List.foldl_cons, hp, ↓reduceDIte, List.map_cons, List.sum_cons]
        refine ⟨hr_sz, ?_⟩
        rw [hr_eq, hs_eq]; ring
  have hinit_sz : (Array.replicate nv (0 : Int)).size = nv := Array.size_replicate
  obtain ⟨h1_sz, h1_eq⟩ := hadd_rows ubRows yMults (Array.replicate nv 0) hinit_sz hy hub_entries
  obtain ⟨h2_sz, h2_eq⟩ := hadd_rows eqRows zMults _ h1_sz hz heq_entries
  unfold accumDualCols
  refine ⟨h2_sz, ?_⟩
  rw [h2_eq, h1_eq]
  have h0 : (∑ j : Fin nv, (((Array.replicate nv (0 : Int))[j.val]'(by rw [hinit_sz]; exact j.isLt)) : ℚ) * x j) = 0 := by
    apply Finset.sum_eq_zero; intro j _; simp
  rw [h0, zero_add]

/-- Exact rational `ker(D)` rank difference `(rankKerD m s - rankKerD (m - k) (s - d)) / m^2`. -/
def rankDiffQ (d m s k : ℕ) : ℚ :=
  ((rankKerD m s - rankKerD (m - k) (s - d) : ℕ) : ℚ) / ((m : ℚ) * (m : ℚ))

theorem checkT4Bucket_sound {nv : Nat} (ubRows eqRows : Array SparseRow)
    (cLoNum cLoDen cHiNum cHiDen : Nat) (b : T4BucketCert)
    (hchk : checkT4Bucket nv ubRows eqRows cLoNum cLoDen cHiNum cHiDen b = true)
    (hubD : ∀ i (hi : i < ubRows.size), 0 < (ubRows[i]).rhsDen)
    (heqD : ∀ i (hi : i < eqRows.size), 0 < (eqRows[i]).rhsDen)
    (hubE : ∀ i (hi : i < ubRows.size), ∀ e ∈ (ubRows[i]).entries, e.1 < nv)
    (heqE : ∀ i (hi : i < eqRows.size), ∀ e ∈ (eqRows[i]).entries, e.1 < nv)
    (x : Fin nv → ℚ) (hx0 : ∀ j, 0 ≤ x j)
    (hub_sat : ∀ i (hi : i < ubRows.size),
      ((ubRows[i]).entries.map fun e => if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum ≤
        (BASE_DEN : ℚ) * ((ubRows[i]).rhsNum : ℚ) / ((ubRows[i]).rhsDen : ℚ))
    (heq_sat : ∀ i (hi : i < eqRows.size),
      ((eqRows[i]).entries.map fun e => if hj : e.1 < nv then (e.2 : ℚ) * x ⟨e.1, hj⟩ else 0).sum =
        (BASE_DEN : ℚ) * ((eqRows[i]).rhsNum : ℚ) / ((eqRows[i]).rhsDen : ℚ)) :
    (b.m = 0 → False) ∧
    (0 < b.m →
      ∃ (h5 : 5 < nv),
        let ic : Fin nv := ⟨nv - 1, by omega⟩
        ((cLoNum : ℚ) / (cLoDen : ℚ) ≤ x ic) → (x ic ≤ (cHiNum : ℚ) / (cHiDen : ℚ)) →
        (b.δNum : ℚ) / (b.δDen : ℚ) <
          vquotLbQ 1 b.m b.s (x ic) -
            ((∑ k : Fin 4, rankDiffQ 1 b.m b.s k.val * x ⟨k.val, by omega⟩) +
              (rankDiffQ 1 b.m b.s 3 - rankDiffQ 1 b.m b.s 2) * x ⟨4, by omega⟩) ∧
        checkCapWitness 1 b.m b.s cHiNum cHiDen b.δNum b.δDen b.hiGNum b.hiGDen 1 b.cap1 = true ∧
        checkCapWitness 1 b.m b.s cHiNum cHiDen b.δNum b.δDen b.hiGNum b.hiGDen 2 b.cap2 = true) := by
  unfold checkT4Bucket at hchk
  dsimp only at hchk
  by_cases h1 : (nv < 6 || cLoDen == 0 || cHiDen == 0 || b.scaleS ≤ 0) = true
  · rw [if_pos h1] at hchk; cases hchk
  rw [if_neg h1] at hchk
  by_cases h2 : (!b.yMults.all (fun x => decide (x.1 < ubRows.size) && decide (0 ≤ x.2))) = true
  · rw [if_pos h2] at hchk; cases hchk
  rw [if_neg h2] at hchk
  by_cases h3 : (!b.zMults.all (fun x => decide (x.1 < eqRows.size))) = true
  · rw [if_pos h3] at hchk; cases hchk
  rw [if_neg h3] at hchk
  by_cases h4 : (!decide ((cLoNum : ℤ) * (cHiDen : ℤ) < (cHiNum : ℤ) * (cLoDen : ℤ))) = true
  · rw [if_pos h4] at hchk; cases hchk
  rw [if_neg h4] at hchk
  have hnv : 6 ≤ nv := by by_contra h; simp [show nv < 6 by omega] at h1
  have hcLoD : 0 < cLoDen := by by_contra h; simp [show cLoDen = 0 by omega] at h1
  have hcHiD : 0 < cHiDen := by by_contra h; simp [show cHiDen = 0 by omega] at h1
  have hSpos : 0 < b.scaleS := by by_contra h; simp [show b.scaleS ≤ 0 by omega] at h1
  have hyAll : ∀ p ∈ b.yMults, p.1 < ubRows.size ∧ 0 ≤ p.2 := by
    have h' : b.yMults.all (fun p => decide (p.1 < ubRows.size) && decide (0 ≤ p.2)) = true := by
      cases hall : b.yMults.all (fun p => decide (p.1 < ubRows.size) && decide (0 ≤ p.2))
      · simp [hall] at h2
      · rfl
    intro p hp
    have := List.all_eq_true.mp h' p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  have hzAll : ∀ p ∈ b.zMults, p.1 < eqRows.size := by
    have h' : b.zMults.all (fun p => decide (p.1 < eqRows.size)) = true := by
      cases hall : b.zMults.all (fun p => decide (p.1 < eqRows.size))
      · simp [hall] at h3
      · rfl
    intro p hp
    exact decide_eq_true_eq.mp (List.all_eq_true.mp h' p hp)
  have hcltZ : (cLoNum : ℤ) * cHiDen < (cHiNum : ℤ) * cLoDen := by
    have h' : decide ((cLoNum : ℤ) * cHiDen < (cHiNum : ℤ) * cLoDen) = true := by
      cases hb : decide ((cLoNum : ℤ) * cHiDen < (cHiNum : ℤ) * cLoDen)
      · simp [hb] at h4
      · rfl
    exact decide_eq_true_eq.mp h'
  have hBpos : (0 : ℚ) < (BASE_DEN : ℚ) := by norm_num [BASE_DEN, N]
  obtain ⟨hcols_sz, hdot_eq⟩ := accumDualCols_dot ubRows eqRows b.yMults b.zMults x
    (fun p hp => (hyAll p hp).1) hzAll hubE heqE
  have hrhs := dualRhsFrac_val ubRows eqRows b.yMults b.zMults
    (fun p hp => (hyAll p hp).1) hzAll hubD heqD
  set cols := accumDualCols nv ubRows eqRows b.yMults b.zMults
  set rhsP := dualRhsFrac ubRows eqRows b.yMults b.zMults
  have hpd : (∑ j : Fin nv, (cols[j.val]'(by omega) : ℚ) * x j) ≤
      (BASE_DEN : ℚ) * ((rhsP.1 : ℚ) / (rhsP.2 : ℚ)) := by
    rw [hdot_eq, hrhs.2, mul_add]
    have hlist_le : ∀ (ms : List (Nat × Int)) (f g : (Nat × Int) → ℚ),
        (∀ p ∈ ms, f p ≤ g p) → (ms.map f).sum ≤ (ms.map g).sum := by
      intro ms f g hfg
      induction ms with
      | nil => simp
      | cons a t ih =>
          simp only [List.map_cons, List.sum_cons]
          exact add_le_add (hfg a (by simp)) (ih fun p hp => hfg p (by simp [hp]))
    have hlist_mul : ∀ (ms : List (Nat × Int)) (c : ℚ) (g : (Nat × Int) → ℚ),
        c * (ms.map g).sum = (ms.map fun p => c * g p).sum := by
      intro ms c g
      induction ms with
      | nil => simp
      | cons a t ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]
    apply add_le_add
    · rw [hlist_mul]; apply hlist_le; intro p hp
      have ⟨hpr, hpy⟩ := hyAll p hp
      simp only [hpr, ↓reduceDIte]
      have hpyQ : (0 : ℚ) ≤ (p.2 : ℚ) := by exact_mod_cast hpy
      have hsat := hub_sat p.1 hpr
      have hmul := mul_le_mul_of_nonneg_left hsat hpyQ
      calc _ ≤ (p.2 : ℚ) * ((BASE_DEN : ℚ) * ((ubRows[p.1]).rhsNum : ℚ) / ((ubRows[p.1]).rhsDen : ℚ)) := hmul
        _ = (BASE_DEN : ℚ) * ((p.2 : ℚ) * ((ubRows[p.1]).rhsNum : ℚ) / ((ubRows[p.1]).rhsDen : ℚ)) := by ring
    · rw [hlist_mul]; apply le_of_eq; congr 1; apply List.map_congr_left; intro p hp
      have hpe := hzAll p hp
      simp only [hpe, ↓reduceDIte, heq_sat p.1 hpe]; ring
  have hrhsD_not : ¬ rhsP.2 ≤ 0 := by omega
  change (if rhsP.2 ≤ 0 then false else _) = true at hchk
  rw [if_neg hrhsD_not] at hchk
  by_cases hm0 : (b.m == 0) = true
  · rw [if_pos hm0] at hchk
    have hm0' : b.m = 0 := beq_iff_eq.mp hm0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨hcols_nn, hrhs_neg⟩
    refine ⟨fun _ => ?_, fun hpos => by omega⟩
    have hsum_nn : 0 ≤ ∑ j : Fin nv, (cols[j.val]'(by omega) : ℚ) * x j := by
      apply Finset.sum_nonneg; intro j _
      have hj_mem : cols[j.val]'(by omega) ∈ cols.toList := by
        rw [Array.mem_toList_iff]
        exact Array.getElem_mem (by omega)
      have hj : 0 ≤ cols[j.val]'(by omega) :=
        decide_eq_true_eq.mp (List.all_eq_true.mp hcols_nn _ hj_mem)
      exact mul_nonneg (by exact_mod_cast hj) (hx0 j)
    have hnegQ : (BASE_DEN : ℚ) * ((rhsP.1 : ℚ) / (rhsP.2 : ℚ)) < 0 := by
      have h1 : (rhsP.1 : ℚ) < 0 := by exact_mod_cast hrhs_neg
      have h2 : (0 : ℚ) < (rhsP.2 : ℚ) := by exact_mod_cast hrhs.1
      have : (rhsP.1 : ℚ) / (rhsP.2 : ℚ) < 0 := div_neg_of_neg_of_pos h1 h2
      exact mul_neg_of_pos_of_neg hBpos this
    linarith
  · rw [if_neg hm0] at hchk
    have hm_ne : b.m ≠ 0 := fun h => hm0 (beq_iff_eq.mpr h)
    have hm_pos : 0 < b.m := Nat.pos_of_ne_zero hm_ne
    by_cases hbadms : (b.s < 1 || b.δNum == 0 || b.δDen == 0) = true
    · rw [if_pos hbadms] at hchk; cases hchk
    rw [if_neg hbadms] at hchk
    have hs1 : 1 ≤ b.s := by by_contra h; simp [show b.s < 1 by omega] at hbadms
    have hδN : 0 < b.δNum := by by_contra h; simp [show b.δNum = 0 by omega] at hbadms
    have hδD : 0 < b.δDen := by by_contra h; simp [show b.δDen = 0 by omega] at hbadms
    refine ⟨fun h => absurd h hm_ne, fun _ => ⟨by omega, ?_⟩⟩
    dsimp only
    intro hlo hhi
    simp only [Bool.and_eq_true] at hchk
    rcases hchk with ⟨⟨⟨⟨hcolsB, hcolIc⟩, hobj⟩, hcap1⟩, hcap2⟩
    refine ⟨?_, hcap1, hcap2⟩
    -- Unpack all rational quantities!
    have hcLoDQ : (0 : ℚ) < (cLoDen : ℚ) := by exact_mod_cast hcLoD
    have hcHiDQ : (0 : ℚ) < (cHiDen : ℚ) := by exact_mod_cast hcHiD
    have hcltQ : (cLoNum : ℚ) / (cLoDen : ℚ) < (cHiNum : ℚ) / (cHiDen : ℚ) := by
      rw [div_lt_div_iff₀ hcLoDQ hcHiDQ]; exact_mod_cast hcltZ
    have hSposQ : (0 : ℚ) < (b.scaleS : ℚ) := by exact_mod_cast hSpos
    have hmQ : (0 : ℚ) < (b.m : ℚ) := by exact_mod_cast hm_pos
    have hm2Q : (0 : ℚ) < (b.m : ℚ) * (b.m : ℚ) := by positivity
    set cLoQ : ℚ := (cLoNum : ℚ) / (cLoDen : ℚ)
    set cHiQ : ℚ := (cHiNum : ℚ) / (cHiDen : ℚ)
    set vLoN : ℤ := vquotNum 1 b.m b.s cLoNum cLoDen
    set vLoD : ℤ := vquotDen b.m cLoDen
    set vHiN : ℤ := vquotNum 1 b.m b.s cHiNum cHiDen
    set vHiD : ℤ := vquotDen b.m cHiDen
    have hvLoD_pos : 0 < vLoD := vquotDen_pos hm_pos (by exact_mod_cast hcLoD)
    have hvHiD_pos : 0 < vHiD := vquotDen_pos hm_pos (by exact_mod_cast hcHiD)
    have hvLo_eq : (vLoN : ℚ) / (vLoD : ℚ) = vquotLbQ 1 b.m b.s cLoQ :=
      vquotNum_div_eq 1 b.m b.s hm_pos cLoNum cLoDen (by exact_mod_cast hcLoD)
    have hvHi_eq : (vHiN : ℚ) / (vHiD : ℚ) = vquotLbQ 1 b.m b.s cHiQ :=
      vquotNum_div_eq 1 b.m b.s hm_pos cHiNum cHiDen (by exact_mod_cast hcHiD)
    set slNum : ℤ := (vHiN * vLoD - vLoN * vHiD) * ((cLoDen : ℤ) * (cHiDen : ℤ))
    set slDen : ℤ := (vLoD * vHiD) * ((cHiNum : ℤ) * (cLoDen : ℤ) - (cLoNum : ℤ) * (cHiDen : ℤ))
    have hslDen_pos : 0 < slDen := mul_pos (mul_pos hvLoD_pos hvHiD_pos) (by omega)
    have hsl_eq : (slNum : ℚ) / (slDen : ℚ) = (vquotLbQ 1 b.m b.s cHiQ - vquotLbQ 1 b.m b.s cLoQ) / (cHiQ - cLoQ) := by
      rw [← hvLo_eq, ← hvHi_eq]
      have h1 : (vLoD : ℚ) ≠ 0 := by exact_mod_cast hvLoD_pos.ne'
      have h2 : (vHiD : ℚ) ≠ 0 := by exact_mod_cast hvHiD_pos.ne'
      have h3 : (cHiQ - cLoQ) ≠ 0 := (sub_pos.mpr hcltQ).ne'
      have h4 : (slDen : ℚ) ≠ 0 := by exact_mod_cast hslDen_pos.ne'
      dsimp only [slNum, slDen, cLoQ, cHiQ]
      push_cast
      field_simp [h1, h2, hcLoDQ.ne', hcHiDQ.ne', h3, h4]
    set vSlQ : ℚ := (vquotLbQ 1 b.m b.s cHiQ - vquotLbQ 1 b.m b.s cLoQ) / (cHiQ - cLoQ)
    -- Step B6402HybridP64.A: Column lower bounds for every j : Fin nv!
    have hrk_le : ∀ k : ℕ, rankKerD (b.m - k) (b.s - 1) ≤ rankKerD b.m b.s := fun k =>
      (rankKerD_mono_left (b.s - 1) (Nat.sub_le b.m k)).trans (rankKerD_mono_right b.m (Nat.sub_le b.s 1))
    have hrk_cast : ∀ k : ℕ,
        (((rankKerD b.m b.s : ℤ) - (rankKerD (b.m - k) (b.s - 1) : ℤ)) : ℚ) / ((b.m : ℚ) * (b.m : ℚ)) =
        rankDiffQ 1 b.m b.s k := by
      intro k; unfold rankDiffQ; rw [Nat.cast_sub (hrk_le k)]; push_cast; rfl
    have hcol_basic : ∀ j : Fin nv,
        (j.val < 4 → (BASE_DEN : ℚ) * (b.scaleS : ℚ) * rankDiffQ 1 b.m b.s j.val ≤ (cols[j.val]'(by omega) : ℚ)) ∧
        (j.val = 4 → (BASE_DEN : ℚ) * (b.scaleS : ℚ) * (rankDiffQ 1 b.m b.s 3 - rankDiffQ 1 b.m b.s 2) ≤ (cols[j.val]'(by omega) : ℚ)) ∧
        (5 ≤ j.val → j.val ≠ nv - 1 → (0 : ℚ) ≤ (cols[j.val]'(by omega) : ℚ)) := by
      intro j
      have hmem : j.val ∈ List.range nv := List.mem_range.mpr j.isLt
      have hj_ok := List.all_eq_true.mp hcolsB j.val hmem
      have hj_sz : j.val < cols.size := by omega
      simp only [hj_sz, ↓reduceDIte] at hj_ok
      refine ⟨fun hj4 => ?_, fun hj4 => ?_, fun hj5 hjne => ?_⟩
      · have hj5 : j.val < 5 := by omega
        simp only [hj5, ↓reduceIte, decide_eq_true_eq] at hj_ok
        have hZ : BASE_DEN * b.scaleS * ((rankKerD b.m b.s : ℤ) - (rankKerD (b.m - j.val) (b.s - 1) : ℤ)) ≤
            cols[j.val] * ((b.m : ℤ) * (b.m : ℤ)) := by
          rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 by omega) with h | h | h | h <;>
            · simp only [h] at hj_ok ⊢; exact hj_ok
        have hQ : (BASE_DEN : ℚ) * (b.scaleS : ℚ) *
            (((rankKerD b.m b.s : ℤ) - (rankKerD (b.m - j.val) (b.s - 1) : ℤ)) : ℚ) ≤
            (cols[j.val] : ℚ) * ((b.m : ℚ) * (b.m : ℚ)) := by exact_mod_cast hZ
        rw [← hrk_cast j.val, mul_div_assoc', div_le_iff₀ hm2Q]; exact hQ
      · have hj5 : j.val < 5 := by omega
        simp only [hj5, ↓reduceIte, decide_eq_true_eq] at hj_ok
        have hZ : BASE_DEN * b.scaleS *
            (((rankKerD b.m b.s : ℤ) - (rankKerD (b.m - 3) (b.s - 1) : ℤ)) -
             ((rankKerD b.m b.s : ℤ) - (rankKerD (b.m - 2) (b.s - 1) : ℤ))) ≤
            cols[j.val] * ((b.m : ℤ) * (b.m : ℤ)) := by
          simp only [hj4] at hj_ok ⊢; exact hj_ok
        have hQ : (BASE_DEN : ℚ) * (b.scaleS : ℚ) *
            ((((rankKerD b.m b.s : ℤ) - (rankKerD (b.m - 3) (b.s - 1) : ℤ)) : ℚ) -
             (((rankKerD b.m b.s : ℤ) - (rankKerD (b.m - 2) (b.s - 1) : ℤ)) : ℚ)) ≤
            (cols[j.val] : ℚ) * ((b.m : ℚ) * (b.m : ℚ)) := by exact_mod_cast hZ
        rw [← hrk_cast 3, ← hrk_cast 2, ← sub_div, mul_div_assoc', div_le_iff₀ hm2Q]; exact hQ
      · have hnot5 : ¬ j.val < 5 := by omega
        have hne_b : (j.val == nv - 1) = false := beq_false_of_ne hjne
        simp only [hnot5, hne_b, ↓reduceIte, Bool.false_eq_true, decide_eq_true_eq] at hj_ok
        exact_mod_cast hj_ok
    have hcol_ic : -(BASE_DEN : ℚ) * (b.scaleS : ℚ) * vSlQ ≤ (cols[nv - 1]'(by omega) : ℚ) := by
      have hic_sz : nv - 1 < cols.size := by omega
      simp only [hic_sz, ↓reduceDIte, decide_eq_true_eq] at hcolIc
      have hQ : (0 : ℚ) ≤ (cols[nv - 1] : ℚ) * (slDen : ℚ) + (BASE_DEN : ℚ) * (b.scaleS : ℚ) * (slNum : ℚ) := by
        exact_mod_cast hcolIc
      have hslD_posQ : (0 : ℚ) < (slDen : ℚ) := by exact_mod_cast hslDen_pos
      rw [← hsl_eq]
      have : -(BASE_DEN : ℚ) * (b.scaleS : ℚ) * ((slNum : ℚ) / (slDen : ℚ)) =
          (-(BASE_DEN : ℚ) * (b.scaleS : ℚ) * (slNum : ℚ)) / (slDen : ℚ) := by ring
      rw [this, div_le_iff₀ hslD_posQ]; linarith
    -- Step B: Multiply column bounds by x j ≥ 0 and sum over Fin nv!
    let cvec (j : Fin nv) : ℚ :=
      if h4 : j.val < 4 then (BASE_DEN : ℚ) * (b.scaleS : ℚ) * rankDiffQ 1 b.m b.s j.val
      else if j.val = 4 then (BASE_DEN : ℚ) * (b.scaleS : ℚ) * (rankDiffQ 1 b.m b.s 3 - rankDiffQ 1 b.m b.s 2)
      else if j.val = nv - 1 then -(BASE_DEN : ℚ) * (b.scaleS : ℚ) * vSlQ
      else 0
    have hcvec_le : ∀ j : Fin nv, cvec j * x j ≤ (cols[j.val]'(by omega) : ℚ) * x j := by
      intro j; apply mul_le_mul_of_nonneg_right _ (hx0 j)
      dsimp only [cvec]
      split_ifs with h1' h2' h3'
      · exact (hcol_basic j).1 h1'
      · exact (hcol_basic j).2.1 h2'
      · simp only [h3']; exact hcol_ic
      · exact (hcol_basic j).2.2 (by omega) h3'
    have hsum_cvec : (∑ j : Fin nv, cvec j * x j) =
        (BASE_DEN : ℚ) * (b.scaleS : ℚ) *
          ((∑ k : Fin 4, rankDiffQ 1 b.m b.s k.val * x ⟨k.val, by omega⟩) +
            (rankDiffQ 1 b.m b.s 3 - rankDiffQ 1 b.m b.s 2) * x ⟨4, by omega⟩ -
            vSlQ * x ⟨nv - 1, by omega⟩) := by
      let S4 : Finset (Fin nv) := Finset.univ.filter fun j : Fin nv => j.val < 4
      let j4 : Fin nv := ⟨4, by omega⟩
      let jic : Fin nv := ⟨nv - 1, by omega⟩
      have h4_not : j4 ∉ S4 := by simp [S4, j4]
      have hic_not : jic ∉ insert j4 S4 := by simp [S4, j4, jic]; omega
      have hsupp : ∑ j : Fin nv, cvec j * x j = ∑ j ∈ insert jic (insert j4 S4), cvec j * x j := by
        symm; apply Finset.sum_subset (Finset.subset_univ _); intro j _ hj
        simp only [Finset.mem_insert, S4, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hj
        have hne_ic : j.val ≠ nv - 1 := fun h => hj.1 (Fin.ext h)
        have hne_4 : j.val ≠ 4 := fun h => hj.2.1 (Fin.ext h)
        have hnot4 : ¬ j.val < 4 := hj.2.2
        simp [cvec, hnot4, hne_4, hne_ic]
      rw [hsupp, Finset.sum_insert hic_not, Finset.sum_insert h4_not]
      have hS4_sum : ∑ j ∈ S4, cvec j * x j =
          ∑ k : Fin 4, (BASE_DEN : ℚ) * (b.scaleS : ℚ) * rankDiffQ 1 b.m b.s k.val * x ⟨k.val, by omega⟩ := by
        refine Finset.sum_bij (fun (j : Fin nv) (hj : j ∈ S4) => ⟨j.val, (Finset.mem_filter.mp hj).2⟩) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro a _ b' _ hab; exact Fin.ext (Fin.mk.inj hab)
        · intro k _
          exact ⟨⟨k.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩, Fin.ext rfl⟩
        · intro j hj
          have hj4 : j.val < 4 := (Finset.mem_filter.mp hj).2
          simp [cvec, hj4]
      rw [hS4_sum]
      have hj4_val : cvec j4 * x j4 =
          (BASE_DEN : ℚ) * (b.scaleS : ℚ) * (rankDiffQ 1 b.m b.s 3 - rankDiffQ 1 b.m b.s 2) * x j4 := by
        simp [cvec, j4]
      have hjic_val : cvec jic * x jic =
          -(BASE_DEN : ℚ) * (b.scaleS : ℚ) * vSlQ * x jic := by
        have h1' : ¬ nv - 1 < 4 := by omega
        have h2' : nv - 1 ≠ 4 := by omega
        simp [cvec, jic, h1', h2']
      have hpull : (∑ k : Fin 4, (BASE_DEN : ℚ) * (b.scaleS : ℚ) * rankDiffQ 1 b.m b.s k.val * x ⟨k.val, by omega⟩) =
          (BASE_DEN : ℚ) * (b.scaleS : ℚ) * (∑ k : Fin 4, rankDiffQ 1 b.m b.s k.val * x ⟨k.val, by omega⟩) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      rw [hj4_val, hjic_val, hpull]; dsimp only [j4, jic]; ring
    have hsum_le : (BASE_DEN : ℚ) * (b.scaleS : ℚ) *
        ((∑ k : Fin 4, rankDiffQ 1 b.m b.s k.val * x ⟨k.val, by omega⟩) +
          (rankDiffQ 1 b.m b.s 3 - rankDiffQ 1 b.m b.s 2) * x ⟨4, by omega⟩ -
          vSlQ * x ⟨nv - 1, by omega⟩) ≤
        (BASE_DEN : ℚ) * ((rhsP.1 : ℚ) / (rhsP.2 : ℚ)) := by
      rw [← hsum_cvec]
      exact (Finset.sum_le_sum fun j _ => hcvec_le j).trans hpd
    have hdiv_pd : (∑ k : Fin 4, rankDiffQ 1 b.m b.s k.val * x ⟨k.val, by omega⟩) +
        (rankDiffQ 1 b.m b.s 3 - rankDiffQ 1 b.m b.s 2) * x ⟨4, by omega⟩ -
        vSlQ * x ⟨nv - 1, by omega⟩ ≤ ((rhsP.1 : ℚ) / (rhsP.2 : ℚ)) / (b.scaleS : ℚ) := by
      have hBS : (0 : ℚ) < (BASE_DEN : ℚ) * (b.scaleS : ℚ) := mul_pos hBpos hSposQ
      rw [le_div_iff₀ hSposQ]
      nlinarith only [hsum_le, hBpos]
    -- Step C: Strict objective bound from hobj!
    have hobj_Q : (b.δNum : ℚ) / (b.δDen : ℚ) <
        vquotLbQ 1 b.m b.s cLoQ - vSlQ * cLoQ - ((rhsP.1 : ℚ) / (rhsP.2 : ℚ)) / (b.scaleS : ℚ) := by
      have hobjZ := decide_eq_true_eq.mp hobj
      set v0Num : ℤ := vLoN * slDen * (cLoDen : ℤ) - slNum * (cLoNum : ℤ) * vLoD
      set v0Den : ℤ := vLoD * slDen * (cLoDen : ℤ)
      have hv0D_pos : 0 < v0Den := mul_pos (mul_pos hvLoD_pos hslDen_pos) (by exact_mod_cast hcLoD)
      have hobjQ' : (b.δNum : ℚ) * (v0Den : ℚ) * (b.scaleS : ℚ) * (rhsP.2 : ℚ) <
          ((v0Num : ℚ) * (b.scaleS : ℚ) * (rhsP.2 : ℚ) - (rhsP.1 : ℚ) * (v0Den : ℚ)) * (b.δDen : ℚ) := by
        exact_mod_cast hobjZ
      have hv0_eq : (v0Num : ℚ) / (v0Den : ℚ) = vquotLbQ 1 b.m b.s cLoQ - vSlQ * cLoQ := by
        rw [← hvLo_eq, ← hsl_eq]
        have h1' : (vLoD : ℚ) ≠ 0 := by exact_mod_cast hvLoD_pos.ne'
        have h2' : (slDen : ℚ) ≠ 0 := by exact_mod_cast hslDen_pos.ne'
        have h3' : (v0Den : ℚ) ≠ 0 := by exact_mod_cast hv0D_pos.ne'
        dsimp only [v0Num, v0Den, cLoQ]
        push_cast; field_simp [h1', h2', h3', hcLoDQ.ne']
      rw [← hv0_eq]
      have h1' : (0 : ℚ) < (v0Den : ℚ) := by exact_mod_cast hv0D_pos
      have h2' : (0 : ℚ) < (rhsP.2 : ℚ) := by exact_mod_cast hrhs.1
      have h3' : (0 : ℚ) < (b.δDen : ℚ) := by exact_mod_cast hδD
      rw [show (v0Num : ℚ) / (v0Den : ℚ) - ((rhsP.1 : ℚ) / (rhsP.2 : ℚ)) / (b.scaleS : ℚ) =
          ((v0Num : ℚ) * (b.scaleS : ℚ) * (rhsP.2 : ℚ) - (rhsP.1 : ℚ) * (v0Den : ℚ)) /
            ((v0Den : ℚ) * (b.scaleS : ℚ) * (rhsP.2 : ℚ)) by field_simp [h1'.ne', h2'.ne', hSposQ.ne']]
      rw [div_lt_div_iff₀ h3' (by positivity)]
      linarith
    -- Step D: Concavity `vquotLbQ_ge_secant` on `[cLoQ, cHiQ]`!
    have hsec := vquotLbQ_ge_secant 1 b.m b.s hm_pos hlo hhi hcltQ
    dsimp only at hsec
    have hsec_rew :
        (1 - (x ⟨nv - 1, by omega⟩ - cLoQ) / (cHiQ - cLoQ)) * vquotLbQ 1 b.m b.s cLoQ +
          (x ⟨nv - 1, by omega⟩ - cLoQ) / (cHiQ - cLoQ) * vquotLbQ 1 b.m b.s cHiQ =
        vquotLbQ 1 b.m b.s cLoQ - vSlQ * cLoQ + vSlQ * x ⟨nv - 1, by omega⟩ := by
      have hden : cHiQ - cLoQ ≠ 0 := (sub_pos.mpr hcltQ).ne'
      dsimp only [vSlQ]; field_simp [hden]; ring
    rw [hsec_rew] at hsec
    linarith

end B6402IntFarkas
end ProximityPrize.SubmissionBinaryLower
