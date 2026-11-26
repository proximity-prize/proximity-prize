import ProximityPrize.SubmissionBinaryLower.B6401IntFarkas
import ProximityPrize.SubmissionBinaryLower.B6401ResultantOrd
import Mathlib.Tactic

set_option Elab.async false
set_option maxHeartbeats 2400000

/-!
# Pure-`Int` Kernel-`decide` Verifiers for Tables 1, 2, 3, and 3-2B (`B6401IntSmallCerts`)

Every checker in this module uses ONLY exact `Int`/`Nat` arithmetic (ZERO `ℚ`, ZERO `Nat.gcd`)
so that all 2,088 certificates across Tables 1, 2, 3, and 3-2B verify instantaneously via kernel
`decide` (zero `native_decide`, standard axioms only!).

Soundness theorems bridge directly to:
- `vquotLbQ d m s c` (via `vquotNum`/`vquotDen` and `vquotLbQ_ge_secant`),
- `rankDiffQ d m s k` (with proved global convexity `rankKerD_convex` handling ALL unbounded `k : ℕ`!),
- `checkCapWitness` (already proved sound in `B6401IntFarkas`).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401IntSmallCerts

open B6401Params B6401ContactKerD B6401FarkasVerifier B6401ResultantOrd B6401IntFarkas
open scoped BigOperators

/-! ### Part 0: Global convexity of `rankKerD` in `m` and exact `resOrdWeighted` large-`mf` closed form -/

private lemma linear_interp_eq {a b x : ℚ} (h : a < b) :
    x = (1 - (x - a) / (b - a)) * a + ((x - a) / (b - a)) * b := by
  have hne : b - a ≠ 0 := (sub_pos.mpr h).ne'
  field_simp [hne]; ring

private lemma resOrdExact_4_2_grow (a0 d0 p q2 r : ℕ)
    (ha : 0 < p + r → 5 ≤ a0) (hd : 0 < q2 + r → 2 ≤ d0) :
    resOrdExact 4 (a0 - 1) 2 d0 + 2 * p + 4 * q2 + 6 * r ≤
      resOrdExact 4 (a0 + p + r - 1) 2 (d0 + q2 + r) := by
  unfold resOrdExact; simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  by_cases hpr : p + r = 0
  · by_cases hqr : q2 + r = 0
    · have : p = 0 ∧ q2 = 0 ∧ r = 0 := by omega
      rcases this with ⟨rfl, rfl, rfl⟩; simp
    · have hd2 := hd (Nat.pos_of_ne_zero hqr)
      have : p = 0 ∧ r = 0 := by omega
      rcases this with ⟨rfl, rfl⟩
      rw [show 2 - d0 = 0 by omega, show 2 - (d0 + q2 + 0) = 0 by omega]
      simp only [mul_zero, add_zero]; omega
  · have ha5 := ha (Nat.pos_of_ne_zero hpr)
    by_cases hqr : q2 + r = 0
    · have : q2 = 0 ∧ r = 0 := by omega
      rcases this with ⟨rfl, rfl⟩
      rw [show 4 - (a0 - 1) = 0 by omega, show 4 - (a0 + p + 0 - 1) = 0 by omega]
      simp only [zero_mul, add_zero]; omega
    · have hd2 := hd (Nat.pos_of_ne_zero hqr)
      rw [show 4 - (a0 - 1) = 0 by omega, show 4 - (a0 + p + r - 1) = 0 by omega]
      simp only [zero_mul, add_zero]; omega

private lemma convex_comb_lt {t a b B : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : a < B) (hb : b < B) :
    (1 - t) * a + t * b < B := by
  by_cases ht : t = 0
  · subst ht; linarith
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have h1 : (1 - t) * a ≤ (1 - t) * B := mul_le_mul_of_nonneg_left ha.le (by linarith)
    have h2 : t * b < t * B := mul_lt_mul_of_pos_left hb htpos
    linarith

private lemma rankKerD_mono_s {m s₁ s₂ : ℕ} (h : s₁ ≤ s₂) : rankKerD m s₁ ≤ rankKerD m s₂ := by
  unfold rankKerD
  have hsub : Finset.range (min (s₁ + 1) m) ⊆ Finset.range (min (s₂ + 1) m) :=
    Finset.range_mono (by omega)
  calc ∑ q ∈ Finset.range (min (s₁ + 1) m), _
      ≤ ∑ q ∈ Finset.range (min (s₁ + 1) m),
          ((m - q) * (m - q + 1) / 2 +
            (if q + 1 ≤ s₂ then (m - q) * (m - q + 1) / 2 else 0) +
            if q + 2 ≤ s₂ then (s₂ - 1 - q) * (m - q) else 0) := by
        apply Finset.sum_le_sum; intro q _
        have hmul : (s₁ - 1 - q) * (m - q) ≤ (s₂ - 1 - q) * (m - q) :=
          Nat.mul_le_mul_right _ (by omega)
        apply Nat.add_le_add
        · apply Nat.add_le_add le_rfl
          by_cases h1 : q + 1 ≤ s₁
          · rw [if_pos h1, if_pos (by omega)]
          · rw [if_neg h1]; exact Nat.zero_le _
        · by_cases h2 : q + 2 ≤ s₁
          · rw [if_pos h2, if_pos (by omega)]; exact hmul
          · rw [if_neg h2]; exact Nat.zero_le _
    _ ≤ ∑ q ∈ Finset.range (min (s₂ + 1) m), _ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- Exact first difference `rankKerD (m + 1) s - rankKerD m s` in `ℕ`. -/
def rankKerDStep (m s : ℕ) : ℕ :=
  ∑ q ∈ Finset.range (min (s + 1) (m + 1)),
    ((m + 1 - q) + (if q + 1 ≤ s then (m + 1 - q) else 0) +
      (if q + 2 ≤ s then (s - 1 - q) else 0))

private lemma rankKerD_succ_eq (m s : ℕ) :
    rankKerD (m + 1) s = rankKerD m s + rankKerDStep m s := by
  unfold rankKerD rankKerDStep
  by_cases hsm : s + 1 ≤ m
  · have h1 : min (s + 1) (m + 1) = s + 1 := min_eq_left (by omega)
    have h2 : min (s + 1) m = s + 1 := min_eq_left hsm
    rw [h1, h2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro q hq
    have hqm : q < m := by simp only [Finset.mem_range] at hq; omega
    have htri : (m + 1 - q) * (m + 1 - q + 1) / 2 = (m - q) * (m - q + 1) / 2 + (m + 1 - q) := by
      have heq : m + 1 - q = (m - q) + 1 := by omega
      rw [heq]
      have hnum : ((m - q) + 1) * ((m - q) + 1 + 1) = (m - q) * ((m - q) + 1) + 2 * ((m - q) + 1) := by ring
      rw [hnum, Nat.add_mul_div_left _ _ (by norm_num)]
    have hlin : (s - 1 - q) * (m + 1 - q) = (s - 1 - q) * (m - q) + (s - 1 - q) := by
      have heq : m + 1 - q = (m - q) + 1 := by omega
      rw [heq, Nat.mul_succ]
    simp only [htri, hlin]
    split_ifs <;> omega
  · have h1 : min (s + 1) (m + 1) = m + 1 := min_eq_right (by omega)
    have h2 : min (s + 1) m = m := min_eq_right (by omega)
    rw [h1, h2, Finset.sum_range_succ, Finset.sum_range_succ]
    have hsum :
        (∑ q ∈ Finset.range m,
          ((m + 1 - q) * (m + 1 - q + 1) / 2 +
            (if q + 1 ≤ s then (m + 1 - q) * (m + 1 - q + 1) / 2 else 0) +
            if q + 2 ≤ s then (s - 1 - q) * (m + 1 - q) else 0)) =
        (∑ q ∈ Finset.range m,
          ((m - q) * (m - q + 1) / 2 +
            (if q + 1 ≤ s then (m - q) * (m - q + 1) / 2 else 0) +
            if q + 2 ≤ s then (s - 1 - q) * (m - q) else 0)) +
        (∑ q ∈ Finset.range m,
          ((m + 1 - q) + (if q + 1 ≤ s then (m + 1 - q) else 0) +
            if q + 2 ≤ s then (s - 1 - q) else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro q hq
      have hqm : q < m := Finset.mem_range.mp hq
      have htri : (m + 1 - q) * (m + 1 - q + 1) / 2 = (m - q) * (m - q + 1) / 2 + (m + 1 - q) := by
        have heq : m + 1 - q = (m - q) + 1 := by omega
        rw [heq]
        have hnum : ((m - q) + 1) * ((m - q) + 1 + 1) = (m - q) * ((m - q) + 1) + 2 * ((m - q) + 1) := by ring
        rw [hnum, Nat.add_mul_div_left _ _ (by norm_num)]
      have hlin : (s - 1 - q) * (m + 1 - q) = (s - 1 - q) * (m - q) + (s - 1 - q) := by
        have heq : m + 1 - q = (m - q) + 1 := by omega
        rw [heq, Nat.mul_succ]
      simp only [htri, hlin]
      split_ifs <;> omega
    rw [hsum]
    have hm1 : m + 1 - m = 1 := by omega
    simp only [hm1, Nat.mul_one, show 1 * (1 + 1) / 2 = 1 by rfl]
    split_ifs <;> omega

private lemma rankKerDStep_mono (m s : ℕ) : rankKerDStep m s ≤ rankKerDStep (m + 1) s := by
  unfold rankKerDStep
  have hsub : Finset.range (min (s + 1) (m + 1)) ⊆ Finset.range (min (s + 1) (m + 2)) :=
    Finset.range_mono (by omega)
  calc ∑ q ∈ Finset.range (min (s + 1) (m + 1)), _
      ≤ ∑ q ∈ Finset.range (min (s + 1) (m + 1)),
          ((m + 2 - q) + (if q + 1 ≤ s then (m + 2 - q) else 0) +
            if q + 2 ≤ s then (s - 1 - q) else 0) := by
        apply Finset.sum_le_sum; intro q _
        split_ifs <;> omega
    _ ≤ ∑ q ∈ Finset.range (min (s + 1) (m + 2)), _ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- Monotonicity of `rankKerD m s` in `m`. -/
lemma rankKerD_mono_m {m₁ m₂ s : ℕ} (h : m₁ ≤ m₂) : rankKerD m₁ s ≤ rankKerD m₂ s := by
  induction h with
  | refl => exact le_rfl
  | @step n _ ih =>
    rw [rankKerD_succ_eq]
    omega

/-- Global discrete convexity of `m ↦ rankKerD m s`: second difference is `≥ 0`! -/
lemma rankKerD_second_diff (m s : ℕ) :
    2 * rankKerD (m + 1) s ≤ rankKerD m s + rankKerD (m + 2) s := by
  have h1 := rankKerD_succ_eq m s
  have h2 := rankKerD_succ_eq (m + 1) s
  have h3 := rankKerDStep_mono m s
  rw [show m + 2 = (m + 1) + 1 from rfl, h2, h1]
  omega

/-- Global concavity of `k ↦ rankDiffQ d m s k` for all `k ≥ K0 ≥ 1`! -/
theorem rankDiffQ_le_linear_tail (d m s K0 k : ℕ) (hK0 : 1 ≤ K0) (hk : K0 ≤ k) :
    rankDiffQ d m s k ≤
      rankDiffQ d m s K0 + (rankDiffQ d m s K0 - rankDiffQ d m s (K0 - 1)) * ((k - K0 : ℕ) : ℚ) := by
  have hstep_dec : ∀ j : ℕ,
      (rankKerD (m - j) (s - d) : ℤ) - (rankKerD (m - (j + 1)) (s - d) : ℤ) ≥
      (rankKerD (m - (j + 1)) (s - d) : ℤ) - (rankKerD (m - (j + 2)) (s - d) : ℤ) := by
    intro j
    by_cases hj : j + 2 ≤ m
    · have h1 : m - (j + 1) = (m - (j + 2)) + 1 := by omega
      have h2 : m - j = (m - (j + 2)) + 2 := by omega
      rw [h1, h2]
      have hcvx := rankKerD_second_diff (m - (j + 2)) (s - d)
      omega
    · by_cases hj1 : j + 1 ≤ m
      · have h0 : m - (j + 2) = 0 := by omega
        have h1 : m - (j + 1) = 0 := by omega
        have h2 : m - j = 1 := by omega
        rw [h0, h1, h2]
        have hmono : rankKerD 0 (s - d) ≤ rankKerD 1 (s - d) := rankKerD_mono_m (by omega)
        omega
      · have h0 : m - (j + 2) = 0 := by omega
        have h1 : m - (j + 1) = 0 := by omega
        have h2 : m - j = 0 := by omega
        rw [h0, h1, h2]
  -- By induction on t = k - K0, rankKerD(m - (K0 + t)) ≥ rankKerD(m - K0) - t * (rankKerD(m - (K0-1)) - rankKerD(m - K0))
  have hstep_le : ∀ t : ℕ,
      (rankKerD (m - (K0 + t)) (s - d) : ℤ) - (rankKerD (m - (K0 + t + 1)) (s - d) : ℤ) ≤
      (rankKerD (m - (K0 - 1)) (s - d) : ℤ) - (rankKerD (m - K0) (s - d) : ℤ) := by
    intro t
    induction t with
    | zero =>
      have hK : K0 = (K0 - 1) + 1 := by omega
      have hK1 : K0 + 1 = (K0 - 1) + 2 := by omega
      simpa only [Nat.add_zero, ← hK, ← hK1] using hstep_dec (K0 - 1)
    | succ t ih =>
      have h1 := hstep_dec (K0 + t)
      have h2 : K0 + (t + 1) = K0 + t + 1 := by omega
      have h3 : K0 + t + 1 + 1 = K0 + t + 2 := by omega
      rw [h2, h3]; omega
  have hind : ∀ t : ℕ,
      (rankKerD (m - K0) (s - d) : ℤ) - (rankKerD (m - (K0 + t)) (s - d) : ℤ) ≤
      (t : ℤ) * ((rankKerD (m - (K0 - 1)) (s - d) : ℤ) - (rankKerD (m - K0) (s - d) : ℤ)) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hs := hstep_le t
      have h1 : K0 + (t + 1) = K0 + t + 1 := by omega
      rw [h1]; push_cast; linarith
  have hk_eq : K0 + (k - K0) = k := by omega
  have hZ := hind (k - K0)
  rw [hk_eq] at hZ
  have hQ : ((rankKerD (m - K0) (s - d) : ℚ) - (rankKerD (m - k) (s - d) : ℚ)) ≤
      ((k - K0 : ℕ) : ℚ) * ((rankKerD (m - (K0 - 1)) (s - d) : ℚ) - (rankKerD (m - K0) (s - d) : ℚ)) := by
    exact_mod_cast hZ
  unfold rankDiffQ
  by_cases hm0 : m = 0
  · subst hm0; simp
  · have hle_k : rankKerD (m - k) (s - d) ≤ rankKerD m s :=
      (rankKerD_mono_m (Nat.sub_le m k)).trans (rankKerD_mono_s (Nat.sub_le s d))
    have hle_K0 : rankKerD (m - K0) (s - d) ≤ rankKerD m s :=
      (rankKerD_mono_m (Nat.sub_le m K0)).trans (rankKerD_mono_s (Nat.sub_le s d))
    have hle_K0m : rankKerD (m - (K0 - 1)) (s - d) ≤ rankKerD m s :=
      (rankKerD_mono_m (Nat.sub_le m (K0 - 1))).trans (rankKerD_mono_s (Nat.sub_le s d))
    rw [Nat.cast_sub hle_k, Nat.cast_sub hle_K0, Nat.cast_sub hle_K0m]
    have hm2 : (0 : ℚ) < (m : ℚ) * (m : ℚ) := by
      have : (0 : ℚ) < (m : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
      positivity
    rw [show (((rankKerD m s : ℚ) - (rankKerD (m - K0) (s - d) : ℚ)) / ((m : ℚ) * (m : ℚ)) +
        (((rankKerD m s : ℚ) - (rankKerD (m - K0) (s - d) : ℚ)) / ((m : ℚ) * (m : ℚ)) -
          ((rankKerD m s : ℚ) - (rankKerD (m - (K0 - 1)) (s - d) : ℚ)) / ((m : ℚ) * (m : ℚ))) *
        ((k - K0 : ℕ) : ℚ)) =
        (((rankKerD m s : ℚ) - (rankKerD (m - K0) (s - d) : ℚ)) +
          ((rankKerD (m - (K0 - 1)) (s - d) : ℚ) - (rankKerD (m - K0) (s - d) : ℚ)) * ((k - K0 : ℕ) : ℚ)) /
        ((m : ℚ) * (m : ℚ)) by ring]
    exact div_le_div_of_nonneg_right (by linarith) hm2.le

/-- Exact closed form of `resOrdWeighted df mf dg mg 2` whenever `0 < df`, `0 < dg`, and `2 * df ≤ mf`!
All `df * dg` gains from `f` equal `2`, and EVERY gain in `allGainsSorted` is `≤ 2`, so the top
`df * dg` gains sum to `2 * df * dg`! -/
theorem resOrdWeighted_eq_of_two_mul_le (df mf dg mg : ℕ) (hdf_pos : 0 < df) (hdg_pos : 0 < dg)
    (hmf : 2 * df ≤ mf) :
    resOrdWeighted df mf dg mg 2 = dg * mf + df * mg - 2 * df * dg := by
  have hdf : df ≠ 0 := Nat.ne_of_gt hdf_pos
  have hdg : dg ≠ 0 := Nat.ne_of_gt hdg_pos
  unfold resOrdWeighted
  simp only [hdf, hdg, ↓reduceIte]
  suffices htop : ((allGainsSorted df mf dg mg 2).take (df * dg)).sum = 2 * df * dg by
    rw [htop]
  set L := allGainsSorted df mf dg mg 2
  have hperm : L.Perm ((List.range df).flatMap (fun i => List.replicate dg (stepGain mf 2 i)) ++
      (List.range dg).flatMap (fun j => List.replicate df (stepGain mg 2 j))) :=
    List.mergeSort_perm _ _
  have hle2_all : ∀ x ∈ L, x ≤ 2 := by
    intro x hx
    have hx' := hperm.subset hx
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_replicate] at hx'
    rcases hx' with ⟨i, _, _, rfl⟩ | ⟨j, _, _, rfl⟩ <;> (unfold stepGain; omega)
  have hgf_eq : (List.range df).flatMap (fun i => List.replicate dg (stepGain mf 2 i)) =
      List.replicate (df * dg) 2 := by
    have hstep : ∀ i ∈ List.range df, List.replicate dg (stepGain mf 2 i) = List.replicate dg 2 := by
      intro i hi
      have hi' : i < df := List.mem_range.mp hi
      congr 1; unfold stepGain; omega
    rw [List.flatMap_congr hstep]
    have hrep : ∀ n : ℕ, (List.range n).flatMap (fun _ => List.replicate dg 2) = List.replicate (n * dg) 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, ih, ← List.replicate_add]
        congr 1; ring
    exact hrep df
  have hlen_ge : df * dg ≤ L.length := by
    rw [hperm.length_eq, List.length_append, hgf_eq, List.length_replicate]
    omega
  have htake_len : (L.take (df * dg)).length = df * dg := by
    rw [List.length_take]; omega
  -- Upper bound: every element of L.take (df * dg) is ≤ 2, so sum ≤ 2 * df * dg
  have hup : (L.take (df * dg)).sum ≤ 2 * df * dg := by
    have hall : ∀ x ∈ L.take (df * dg), x ≤ 2 := fun x hx => hle2_all x (List.mem_of_mem_take hx)
    have hsum_le : ∀ (l : List ℕ), (∀ x ∈ l, x ≤ 2) → l.sum ≤ 2 * l.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons a t ih =>
        simp only [List.sum_cons, List.length_cons]
        have ha : a ≤ 2 := hl a (by simp)
        have ht : t.sum ≤ 2 * t.length := ih (fun x hx => hl x (by simp [hx]))
        omega
    have := hsum_le (L.take (df * dg)) hall
    rw [htake_len] at this; linarith
  -- Lower bound: `List.replicate (df * dg) 2` is a sublist of the unsorted list, so by `sum_sublist_le_sum_take_sorted`!
  have hsub : (List.replicate (df * dg) 2).Sublist
      ((List.range df).flatMap (fun i => List.replicate dg (stepGain mf 2 i)) ++
        (List.range dg).flatMap (fun j => List.replicate df (stepGain mg 2 j))) := by
    rw [hgf_eq]
    exact List.sublist_append_left _ _
  have hlo := sum_sublist_le_sum_take_sorted hsub
  rw [List.length_replicate, List.sum_replicate, smul_eq_mul] at hlo
  change df * dg * 2 ≤ (L.take (df * dg)).sum at hlo
  linarith

/-- `O(1)` pure-`ℕ` closed form of `rankKerD m s` (zero `Finset.sum`), so kernel `decide` reduces
Table 3's double loops in milliseconds instead of expanding `Finset.sum` 1M+ times! -/
def sumTri (n : ℕ) : ℕ := n * (n + 1) * (n + 2) / 6

def sumProd (a b n : ℕ) : ℕ :=
  a * b * n + n * (n - 1) * (2 * n - 1) / 6 - (a + b) * (n * (n - 1) / 2)

def rankKerDFast (m s : ℕ) : ℕ :=
  let n0 := min (s + 1) m
  let n1 := min s m
  let n2 := min (s - 1) m
  (sumTri m - sumTri (m - n0)) + (sumTri m - sumTri (m - n1)) + sumProd (s - 1) m n2

private lemma two_dvd_mul_succ (n : ℕ) : 2 ∣ n * (n + 1) := by
  obtain ⟨k, hk⟩ := Nat.even_mul_succ_self n
  exact ⟨k, by omega⟩

private lemma six_dvd_tri (n : ℕ) : 6 ∣ n * (n + 1) * (n + 2) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := two_dvd_mul_succ (n + 1)
    refine ⟨a + b, ?_⟩
    have h1 : (n + 1) * (n + 2) * (n + 3) = n * (n + 1) * (n + 2) + 3 * ((n + 1) * (n + 2)) := by ring
    linarith

private lemma six_mul_sumTri (n : ℕ) : 6 * sumTri n = n * (n + 1) * (n + 2) :=
  Nat.mul_div_cancel' (six_dvd_tri n)

private lemma sumTri_mono {a b : ℕ} (h : a ≤ b) : sumTri a ≤ sumTri b := by
  have ha := six_mul_sumTri a
  have hb := six_mul_sumTri b
  have hle : a * (a + 1) * (a + 2) ≤ b * (b + 1) * (b + 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul h (by omega)) (by omega)
  omega

private lemma sumTri_succ (n : ℕ) : sumTri (n + 1) = sumTri n + (n + 1) * (n + 2) / 2 := by
  have h1 := six_mul_sumTri n
  have h2 : 6 * sumTri (n + 1) = (n + 1) * (n + 2) * (n + 3) := by
    simpa [add_assoc] using six_mul_sumTri (n + 1)
  have h3 : 2 * ((n + 1) * (n + 2) / 2) = (n + 1) * (n + 2) := by
    simpa [add_assoc] using Nat.mul_div_cancel' (two_dvd_mul_succ (n + 1))
  have hid : (n + 1) * (n + 2) * (n + 3) = n * (n + 1) * (n + 2) + 3 * ((n + 1) * (n + 2)) := by ring
  linarith

private lemma sum_tri_range (m n : ℕ) (hn : n ≤ m) :
    (∑ q ∈ Finset.range n, (m - q) * (m - q + 1) / 2) = sumTri m - sumTri (m - n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have hstep : m - n = (m - (n + 1)) + 1 := by omega
    have hstep2 : m - (n + 1) + 2 = m - n + 1 := by omega
    have hst : sumTri (m - n) = sumTri (m - (n + 1)) + (m - n) * (m - n + 1) / 2 := by
      have h0 := sumTri_succ (m - (n + 1))
      rwa [← hstep, hstep2] at h0
    have hmono1 : sumTri (m - n) ≤ sumTri m := sumTri_mono (by omega)
    have hmono2 : sumTri (m - (n + 1)) ≤ sumTri m := sumTri_mono (by omega)
    omega

private lemma six_dvd_sqsum (n : ℕ) : 6 ∣ n * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    cases n with
    | zero => exact ⟨0, rfl⟩
    | succ k =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨a + (k + 1) * (k + 1), ?_⟩
      have h2a : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
      have h2b : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      simp only [Nat.add_sub_cancel] at ha ⊢
      rw [h2a]
      rw [h2b] at ha
      have hid : (k + 2) * (k + 1) * (2 * k + 3) = (k + 1) * k * (2 * k + 1) + 6 * ((k + 1) * (k + 1)) := by ring
      linarith

private lemma two_dvd_linsum (n : ℕ) : 2 ∣ n * (n - 1) := by
  cases n with
  | zero => exact ⟨0, rfl⟩
  | succ k =>
    simp only [Nat.add_sub_cancel]
    rw [mul_comm]
    exact two_dvd_mul_succ k

private lemma sum_prod_range (a b n : ℕ) (ha : n ≤ a) (hb : n ≤ b) :
    (∑ q ∈ Finset.range n, (a - q) * (b - q)) = sumProd a b n := by
  have hZ : ((∑ q ∈ Finset.range n, (a - q) * (b - q) : ℕ) : ℤ) =
      ((a * b * n + n * (n - 1) * (2 * n - 1) / 6 : ℕ) : ℤ) -
      (((a + b) * (n * (n - 1) / 2) : ℕ) : ℤ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.cast_add, ih (by omega) (by omega)]
      have hsq0 : 6 * (n * (n - 1) * (2 * n - 1) / 6) = n * (n - 1) * (2 * n - 1) :=
        Nat.mul_div_cancel' (six_dvd_sqsum n)
      have hsq1 : 6 * ((n + 1) * n * (2 * (n + 1) - 1) / 6) = (n + 1) * n * (2 * (n + 1) - 1) := by
        simpa only [Nat.add_sub_cancel] using Nat.mul_div_cancel' (six_dvd_sqsum (n + 1))
      have hlin0 : 2 * (n * (n - 1) / 2) = n * (n - 1) := Nat.mul_div_cancel' (two_dvd_linsum n)
      have hlin1 : 2 * ((n + 1) * n / 2) = (n + 1) * n := by
        simpa only [Nat.add_sub_cancel] using Nat.mul_div_cancel' (two_dvd_linsum (n + 1))
      have hsq_step : (n + 1) * n * (2 * (n + 1) - 1) / 6 = n * (n - 1) * (2 * n - 1) / 6 + n * n := by
        cases n with
        | zero => simp
        | succ k =>
          have h2a : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
          have h2b : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
          simp only [Nat.add_sub_cancel] at hsq0 hsq1 ⊢
          rw [h2a] at hsq1 ⊢
          rw [h2b] at hsq0 ⊢
          have hid : (k + 2) * (k + 1) * (2 * k + 3) = (k + 1) * k * (2 * k + 1) + 6 * ((k + 1) * (k + 1)) := by ring
          linarith
      have hlin_step : (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
        cases n with
        | zero => simp
        | succ k =>
          have hid : (k + 2) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by ring
          simp only [Nat.add_sub_cancel] at hlin0 hlin1 ⊢
          linarith
      simp only [Nat.add_sub_cancel]
      rw [hsq_step, hlin_step,
        show (((a - n) * (b - n) : ℕ) : ℤ) = ((a : ℤ) - (n : ℤ)) * ((b : ℤ) - (n : ℤ)) by
          rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]]
      push_cast; ring
  have hle : (a + b) * (n * (n - 1) / 2) ≤ a * b * n + n * (n - 1) * (2 * n - 1) / 6 := by
    have hnn : (0 : ℤ) ≤ ((∑ q ∈ Finset.range n, (a - q) * (b - q) : ℕ) : ℤ) := Nat.cast_nonneg _
    rw [hZ] at hnn
    exact_mod_cast sub_nonneg.mp hnn
  unfold sumProd
  have hZ' : ((∑ q ∈ Finset.range n, (a - q) * (b - q) : ℕ) : ℤ) =
      ((a * b * n + n * (n - 1) * (2 * n - 1) / 6 - (a + b) * (n * (n - 1) / 2) : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle]; exact hZ
  exact_mod_cast hZ'

theorem rankKerDFast_eq (m s : ℕ) : rankKerDFast m s = rankKerD m s := by
  unfold rankKerDFast rankKerD
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ q ∈ Finset.range (min (s + 1) m), (m - q) * (m - q + 1) / 2) =
      sumTri m - sumTri (m - min (s + 1) m) := sum_tri_range m (min (s + 1) m) (min_le_right _ _)
  have h2 : (∑ q ∈ Finset.range (min (s + 1) m),
      if q + 1 ≤ s then (m - q) * (m - q + 1) / 2 else 0) =
      sumTri m - sumTri (m - min s m) := by
    have hsub : Finset.range (min s m) ⊆ Finset.range (min (s + 1) m) :=
      Finset.range_mono (min_le_min_right m (Nat.le_succ s))
    rw [← Finset.sum_subset hsub]
    · rw [← sum_tri_range m (min s m) (min_le_right _ _)]
      apply Finset.sum_congr rfl; intro q hq
      have hql : q < min s m := Finset.mem_range.mp hq
      rw [if_pos (by omega)]
    · intro q hq hnot
      have hql : q < min (s + 1) m := Finset.mem_range.mp hq
      have hge : min s m ≤ q := by by_contra hlt; exact hnot (Finset.mem_range.mpr (by omega))
      rw [if_neg (by omega)]
  have h3 : (∑ q ∈ Finset.range (min (s + 1) m),
      if q + 2 ≤ s then (s - 1 - q) * (m - q) else 0) =
      sumProd (s - 1) m (min (s - 1) m) := by
    have hsub : Finset.range (min (s - 1) m) ⊆ Finset.range (min (s + 1) m) :=
      Finset.range_mono (min_le_min_right m (by omega))
    rw [← Finset.sum_subset hsub]
    · rw [← sum_prod_range (s - 1) m (min (s - 1) m) (min_le_left _ _) (min_le_right _ _)]
      apply Finset.sum_congr rfl; intro q hq
      have hql : q < min (s - 1) m := Finset.mem_range.mp hq
      rw [if_pos (by omega)]
    · intro q hq hnot
      have hql : q < min (s + 1) m := Finset.mem_range.mp hq
      have hge : min (s - 1) m ≤ q := by by_contra hlt; exact hnot (Finset.mem_range.mpr (by omega))
      rw [if_neg (by omega)]
  rw [h1, h2, h3]

/-- Exact integer numerator of `rankDiffQ d m s k` over `mDen = if m == 0 then 1 else m * m`. -/
def rankDiffNum (d m s k : ℕ) : ℤ :=
  if m == 0 then 0 else (rankKerDFast m s : ℤ) - (rankKerDFast (m - k) (s - d) : ℤ)

lemma rankDiffNum_div_eq (d m s k : ℕ) (hm : 0 < m) :
    (rankDiffNum d m s k : ℚ) / ((m : ℚ) * (m : ℚ)) = rankDiffQ d m s k := by
  have hmne : (m == 0) = false := by simp [Nat.ne_of_gt hm]
  have hle : rankKerD (m - k) (s - d) ≤ rankKerD m s :=
    (rankKerD_mono_m (Nat.sub_le m k)).trans (rankKerD_mono_s (Nat.sub_le s d))
  unfold rankDiffNum rankDiffQ
  simp only [hmne, Bool.false_eq_true, ↓reduceIte, rankKerDFast_eq, Int.cast_sub, Int.cast_natCast, Nat.cast_sub hle]

/-- Exact `O(1)` pure-`ℕ` equivalent of `resOrdWeighted df mf dg mg 2` (zero `List.mergeSort`),
so kernel `decide` reduces all Table 1 and Table 3 certificates in milliseconds! -/
def resOrdWeighted2Fast (df mf dg mg : ℕ) : ℕ :=
  if df == 0 then dg * mf
  else if dg == 0 then df * mg
  else
    let k := df * dg
    let c2 := dg * min df (mf / 2) + df * min dg (mg / 2)
    let c1 := (if mf % 2 == 1 && mf / 2 < df then dg else 0) +
              (if mg % 2 == 1 && mg / 2 < dg then df else 0)
    let t2 := min k c2
    let t1 := min (k - t2) c1
    dg * mf + df * mg - (2 * t2 + t1)

private lemma stepGain_two_eq (m i : ℕ) :
    stepGain m 2 i = if i < m / 2 then 2 else if i = m / 2 ∧ m % 2 = 1 then 1 else 0 := by
  unfold stepGain; split_ifs <;> omega

private lemma flatMap_stepGain2_counts (d m r : ℕ) :
    let L := (List.range d).flatMap fun i => List.replicate r (stepGain m 2 i)
    L.length = d * r ∧
    L.count 2 = r * min d (m / 2) ∧
    L.count 1 = (if m % 2 = 1 ∧ m / 2 < d then r else 0) ∧
    (∀ a, a ≠ 0 → a ≠ 1 → a ≠ 2 → L.count a = 0) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rcases ih with ⟨hlen, hc2, hc1, hco⟩
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_append, List.length_replicate, List.count_append,
      List.count_replicate]
    rw [hlen, hc2, hc1]
    have hsg := stepGain_two_eq m d
    refine ⟨by ring, ?_, ?_, ?_⟩
    · rw [hsg]
      by_cases hlt : d < m / 2
      · simp only [hlt, ↓reduceIte, beq_self_eq_true]
        rw [show min (d + 1) (m / 2) = min d (m / 2) + 1 by
          rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]]
        ring
      · have hmin : min (d + 1) (m / 2) = min d (m / 2) := by
          rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
        rw [hmin]
        by_cases heq : d = m / 2 ∧ m % 2 = 1
        · simp [hlt, heq]
        · simp [hlt, heq]
    · rw [hsg]
      by_cases hlt : d < m / 2
      · have h1 : ¬ (m % 2 = 1 ∧ m / 2 < d) := by omega
        have h2 : ¬ (m % 2 = 1 ∧ m / 2 ≤ d) := by omega
        simp [hlt, h1, h2]
      · by_cases heq : d = m / 2 ∧ m % 2 = 1
        · have h1 : ¬ (m % 2 = 1 ∧ m / 2 < d) := by omega
          have h2 : m % 2 = 1 ∧ m / 2 ≤ d := by omega
          simp [hlt, heq, h1, h2]
        · have hiff : (m % 2 = 1 ∧ m / 2 ≤ d) ↔ (m % 2 = 1 ∧ m / 2 < d) := by omega
          simp [hlt, heq, hiff]
    · intro a ha0 ha1 ha2
      rw [hco a ha0 ha1 ha2, zero_add, hsg]
      have h0 : (0 == a) = false := beq_false_of_ne (Ne.symm ha0)
      have h1 : (1 == a) = false := beq_false_of_ne (Ne.symm ha1)
      have h2 : (2 == a) = false := beq_false_of_ne (Ne.symm ha2)
      by_cases hlt : d < m / 2
      · simp [hlt, h2]
      · by_cases heq : d = m / 2 ∧ m % 2 = 1
        · simp [hlt, heq, h1]
        · simp [hlt, heq, h0]

theorem resOrdWeighted2Fast_eq (df mf dg mg : ℕ) :
    resOrdWeighted2Fast df mf dg mg = resOrdWeighted df mf dg mg 2 := by
  unfold resOrdWeighted2Fast resOrdWeighted
  by_cases hdf : df = 0
  · subst hdf; simp
  by_cases hdg : dg = 0
  · subst hdg; simp [hdf]
  have hdfB : (df == 0) = false := beq_false_of_ne hdf
  have hdgB : (dg == 0) = false := beq_false_of_ne hdg
  simp only [hdfB, hdgB, Bool.false_eq_true, ↓reduceIte, hdf, hdg]
  congr 1
  unfold allGainsSorted
  set gf := (List.range df).flatMap fun i => List.replicate dg (stepGain mf 2 i)
  set gg := (List.range dg).flatMap fun j => List.replicate df (stepGain mg 2 j)
  set c2 := dg * min df (mf / 2) + df * min dg (mg / 2)
  set c1 := (if mf % 2 == 1 && mf / 2 < df then dg else 0) +
            (if mg % 2 == 1 && mg / 2 < dg then df else 0)
  set c0 := (gf ++ gg).count 0
  set S := List.replicate c2 2 ++ List.replicate c1 1 ++ List.replicate c0 0
  have hgf := flatMap_stepGain2_counts df mf dg
  have hgg := flatMap_stepGain2_counts dg mg df
  have hgf2 : gf.count 2 = dg * min df (mf / 2) := hgf.2.1
  have hgf1 : gf.count 1 = (if mf % 2 = 1 ∧ mf / 2 < df then dg else 0) := hgf.2.2.1
  have hgfo : ∀ a, a ≠ 0 → a ≠ 1 → a ≠ 2 → gf.count a = 0 := hgf.2.2.2
  have hgg2 : gg.count 2 = df * min dg (mg / 2) := hgg.2.1
  have hgg1 : gg.count 1 = (if mg % 2 = 1 ∧ mg / 2 < dg then df else 0) := hgg.2.2.1
  have hggo : ∀ a, a ≠ 0 → a ≠ 1 → a ≠ 2 → gg.count a = 0 := hgg.2.2.2
  have hc1_eq : c1 = (if mf % 2 = 1 ∧ mf / 2 < df then dg else 0) +
      (if mg % 2 = 1 ∧ mg / 2 < dg then df else 0) := by
    dsimp [c1]; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  have hperm_raw : (gf ++ gg).Perm S := by
    rw [List.perm_iff_count]
    intro a
    simp only [S, List.count_append, List.count_replicate]
    by_cases ha0 : a = 0
    · subst ha0; simp [c0, List.count_append]
    by_cases ha1 : a = 1
    · subst ha1; simp [hgf1, hgg1, hc1_eq]
    by_cases ha2 : a = 2
    · subst ha2; simp [hgf2, hgg2, c2]
    · simp [hgfo a ha0 ha1 ha2, hggo a ha0 ha1 ha2, Ne.symm ha0, Ne.symm ha1, Ne.symm ha2]
  have hS_pw : S.Pairwise (· ≥ ·) := by
    dsimp only [S]
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨List.pairwise_replicate.mpr (Or.inr le_rfl),
             List.pairwise_replicate.mpr (Or.inr le_rfl),
             fun x hx y hy => by rw [(List.mem_replicate.mp hx).2, (List.mem_replicate.mp hy).2]; omega⟩,
            List.pairwise_replicate.mpr (Or.inr le_rfl),
            fun x hx y hy => by
              rw [(List.mem_replicate.mp hy).2]
              rcases List.mem_append.mp hx with h | h
              · rw [(List.mem_replicate.mp h).2]; omega
              · rw [(List.mem_replicate.mp h).2]; omega⟩
  have hsort_eq : (gf ++ gg).mergeSort (· ≥ ·) = S :=
    ((List.mergeSort_perm (gf ++ gg) (· ≥ ·)).trans hperm_raw).eq_of_pairwise
      (fun a b _ _ h1 h2 => le_antisymm h2 h1)
      (List.pairwise_mergeSort' (· ≥ ·) (gf ++ gg)) hS_pw
  rw [hsort_eq]
  dsimp only [S]
  rw [List.append_assoc, List.take_append, List.take_replicate, List.length_replicate,
      List.take_append, List.take_replicate, List.length_replicate, List.take_replicate,
      List.sum_append, List.sum_append, List.sum_replicate, List.sum_replicate, List.sum_replicate]
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
  have hsub : df * dg - c2 = df * dg - min (df * dg) c2 := by omega
  rw [hsub]; ring

/-! ### Part 1: Exact `resYKerD1` helper matching `gen_exact_master_6401.py` bit-for-bit -/

def resYKerD1Ord (d0 d1 k : ℕ) : ℕ :=
  if k == 0 then 0
  else
    let dp := max d0 (d1 + 1)
    let dg := d1 / 2
    if dg == 0 then 0
    else
      let vKer := resOrdWeighted2Fast dp (4 * k + 2) dg (2 * k - 1) - 2 * dg
      let vPln := resOrdExact d0 (2 * k - 1) d1 (2 * k - 1) + (dp - d0) * (2 * k - 1 - d1)
      max vKer vPln

def resYKerD1MinLe (d1 k : ℕ) : ℕ :=
  ((List.range (d1 + 2)).map (fun d0 => resYKerD1Ord d0 d1 k)).foldl Nat.min (resYKerD1Ord 0 d1 k)

def resYKerD1Fn (d1 d0Eff k : ℕ) : ℕ :=
  if d0Eff == d1 + 1 then resYKerD1MinLe d1 k else resYKerD1Ord d0Eff d1 k

lemma resYKerD1Ord_large (d0 d1 k : ℕ) (hd1 : 2 ≤ d1) (hk : max d0 (d1 + 1) + 3 ≤ k) :
    resYKerD1Ord d0 d1 k =
      max (d1 / 2 * (4 * k + 2) + max d0 (d1 + 1) * (2 * k - 1) - 2 * max d0 (d1 + 1) * (d1 / 2) - 2 * (d1 / 2))
        ((d1 + max d0 (d1 + 1)) * (2 * k - 1) - max d0 (d1 + 1) * d1) := by
  set dp := max d0 (d1 + 1)
  set dg := d1 / 2
  have hdp_ge : d1 + 1 ≤ dp := le_max_right _ _
  have hd0_le_dp : d0 ≤ dp := le_max_left _ _
  have h2k_ge : 2 * dp + 5 ≤ 2 * k - 1 := by omega
  have hk0 : (k == 0) = false := by simp; omega
  have hdg0 : (d1 / 2 == 0) = false := by simp; omega
  unfold resYKerD1Ord
  simp only [hk0, Bool.false_eq_true, ↓reduceIte, hdg0, resOrdWeighted2Fast_eq]
  change max (resOrdWeighted dp (4 * k + 2) dg (2 * k - 1) 2 - 2 * dg)
      (resOrdExact d0 (2 * k - 1) d1 (2 * k - 1) + (dp - d0) * (2 * k - 1 - d1)) =
    max (dg * (4 * k + 2) + dp * (2 * k - 1) - 2 * dp * dg - 2 * dg)
      ((d1 + dp) * (2 * k - 1) - dp * d1)
  have hker : resOrdWeighted dp (4 * k + 2) dg (2 * k - 1) 2 =
      dg * (4 * k + 2) + dp * (2 * k - 1) - 2 * dp * dg :=
    resOrdWeighted_eq_of_two_mul_le dp (4 * k + 2) dg (2 * k - 1) (by omega) (by dsimp [dg]; omega) (by omega)
  have hpln : resOrdExact d0 (2 * k - 1) d1 (2 * k - 1) + (dp - d0) * (2 * k - 1 - d1) =
      (d1 + dp) * (2 * k - 1) - dp * d1 := by
    unfold resOrdExact
    by_cases hd0 : d0 = 0
    · subst hd0
      have hdp : dp = d1 + 1 := by dsimp [dp]; omega
      simp only [↓reduceIte, Nat.sub_zero]
      have h1 : d1 ≤ 2 * k - 1 := by omega
      have hsub4 : dp * d1 ≤ (d1 + dp) * (2 * k - 1) := by nlinarith
      zify [h1, hsub4]
      ring
    · have hd1ne : d1 ≠ 0 := by omega
      simp only [hd0, hd1ne, ↓reduceIte]
      have h0a : d0 - (2 * k - 1) = 0 := by omega
      have h1a : d1 - (2 * k - 1) = 0 := by omega
      rw [h0a, h1a, Nat.zero_mul, Nat.add_zero]
      have hsub1 : d0 * d1 ≤ d1 * (2 * k - 1) + d0 * (2 * k - 1) := by nlinarith
      have hsub3 : d1 ≤ 2 * k - 1 := by omega
      have hsub4 : dp * d1 ≤ (d1 + dp) * (2 * k - 1) := by nlinarith
      zify [hsub1, hd0_le_dp, hsub3, hsub4]
      ring
  rw [hker, hpln]

lemma resYKerD1Ord_ge_tail (d0 d1 k : ℕ) (hd1 : 2 ≤ d1) (hk : max d0 (d1 + 1) + 3 ≤ k) :
    resYKerD1Ord d0 d1 (max d0 (d1 + 1) + 3) + 2 * (d1 + max d0 (d1 + 1)) * (k - (max d0 (d1 + 1) + 3)) ≤
      resYKerD1Ord d0 d1 k := by
  set dp := max d0 (d1 + 1)
  set K0 := dp + 3
  set dg := d1 / 2
  have hdp_ge : d1 + 1 ≤ dp := le_max_right _ _
  have hK0_eq : K0 = dp + 3 := rfl
  change resYKerD1Ord d0 d1 K0 + 2 * (d1 + dp) * (k - K0) ≤ resYKerD1Ord d0 d1 k
  have h2K0_ge : 2 * dp + 5 ≤ 2 * K0 - 1 := by omega
  have h2k_ge : 2 * dp + 5 ≤ 2 * k - 1 := by omega
  rw [resYKerD1Ord_large d0 d1 K0 hd1 le_rfl, resYKerD1Ord_large d0 d1 k hd1 hk]
  have h2dg : 2 * dg ≤ d1 := Nat.mul_div_le d1 2
  have hdg_pos : 1 ≤ dg := by dsimp [dg]; omega
  by_cases heven : 2 * dg = d1
  · have hK_ker : dg * (4 * K0 + 2) + dp * (2 * K0 - 1) - 2 * dp * dg - 2 * dg =
        (d1 + dp) * (2 * K0 - 1) - dp * d1 + d1 := by
      have h1 : dp * d1 ≤ (d1 + dp) * (2 * K0 - 1) := by nlinarith
      have h2 : 2 * dp * dg ≤ dg * (4 * K0 + 2) + dp * (2 * K0 - 1) := by nlinarith
      have h3 : 2 * dg ≤ dg * (4 * K0 + 2) + dp * (2 * K0 - 1) - 2 * dp * dg := by
        zify [h2]; nlinarith
      zify [h1, h2, h3, show 1 ≤ 2 * K0 by omega]; nlinarith
    have hk_ker : dg * (4 * k + 2) + dp * (2 * k - 1) - 2 * dp * dg - 2 * dg =
        (d1 + dp) * (2 * k - 1) - dp * d1 + d1 := by
      have h1 : dp * d1 ≤ (d1 + dp) * (2 * k - 1) := by nlinarith
      have h2 : 2 * dp * dg ≤ dg * (4 * k + 2) + dp * (2 * k - 1) := by nlinarith
      have h3 : 2 * dg ≤ dg * (4 * k + 2) + dp * (2 * k - 1) - 2 * dp * dg := by
        zify [h2]; nlinarith
      zify [h1, h2, h3, show 1 ≤ 2 * k by omega]; nlinarith
    rw [hK_ker, hk_ker]
    have hm1 : max ((d1 + dp) * (2 * K0 - 1) - dp * d1 + d1) ((d1 + dp) * (2 * K0 - 1) - dp * d1) =
        (d1 + dp) * (2 * K0 - 1) - dp * d1 + d1 := Nat.max_eq_left (by omega)
    have hm2 : max ((d1 + dp) * (2 * k - 1) - dp * d1 + d1) ((d1 + dp) * (2 * k - 1) - dp * d1) =
        (d1 + dp) * (2 * k - 1) - dp * d1 + d1 := Nat.max_eq_left (by omega)
    rw [hm1, hm2]
    have hle1 : dp * d1 ≤ (d1 + dp) * (2 * K0 - 1) := by nlinarith
    have hle2 : dp * d1 ≤ (d1 + dp) * (2 * k - 1) := by nlinarith
    have hK0_le : K0 ≤ k := hk
    zify [hle1, hle2, hK0_le, show 1 ≤ 2 * K0 by omega, show 1 ≤ 2 * k by omega]; ring_nf; linarith
  · have hodd : d1 = 2 * dg + 1 := by omega
    have hleK : dg * (4 * K0 + 2) + dp * (2 * K0 - 1) - 2 * dp * dg - 2 * dg ≤
        (d1 + dp) * (2 * K0 - 1) - dp * d1 := by
      have h1 : dp * d1 ≤ (d1 + dp) * (2 * K0 - 1) := by nlinarith
      have h2 : 2 * dp * dg ≤ dg * (4 * K0 + 2) + dp * (2 * K0 - 1) := by nlinarith
      have h3 : 2 * dg ≤ dg * (4 * K0 + 2) + dp * (2 * K0 - 1) - 2 * dp * dg := by
        zify [h2]; nlinarith
      zify [h1, h2, h3, show 1 ≤ 2 * K0 by omega]; nlinarith
    rw [Nat.max_eq_right hleK]
    refine le_trans ?_ (le_max_right _ _)
    change ((d1 + dp) * (2 * K0 - 1) - dp * d1) + 2 * (d1 + dp) * (k - K0) ≤ (d1 + dp) * (2 * k - 1) - dp * d1
    have hle1 : dp * d1 ≤ (d1 + dp) * (2 * K0 - 1) := by nlinarith
    have hle2 : dp * d1 ≤ (d1 + dp) * (2 * k - 1) := by nlinarith
    have hK0_le : K0 ≤ k := hk
    zify [hle1, hle2, hK0_le, show 1 ≤ 2 * K0 by omega, show 1 ≤ 2 * k by omega]; ring_nf; linarith

lemma resYKerD1Fn_ge_tail (d1 d0Eff k : ℕ) (hd1 : 2 ≤ d1) (hk : max d0Eff (d1 + 1) + 3 ≤ k) :
    resYKerD1Fn d1 d0Eff (max d0Eff (d1 + 1) + 3) +
      2 * (d1 + max d0Eff (d1 + 1)) * (k - (max d0Eff (d1 + 1) + 3)) ≤
      resYKerD1Fn d1 d0Eff k := by
  unfold resYKerD1Fn
  by_cases heq : d0Eff = d1 + 1
  · subst heq
    simp only [beq_self_eq_true, ↓reduceIte]
    unfold resYKerD1MinLe
    have hfold_le : ∀ (f g : ℕ → ℕ) (c : ℕ) (l : List ℕ) (a b : ℕ),
        a + c ≤ b → (∀ x ∈ l, f x + c ≤ g x) →
        (l.map f).foldl Nat.min a + c ≤ (l.map g).foldl Nat.min b := by
      intro f g c l
      induction l with
      | nil => intro a b hab _; simpa using hab
      | cons x xs ih =>
        intro a b hab hfg
        simp only [List.map_cons, List.foldl_cons]
        apply ih
        · have hx := hfg x (by simp)
          change min a (f x) + c ≤ min b (g x)
          omega
        · intro y hy; exact hfg y (by simp [hy])
    have hdp_eq : max (d1 + 1) (d1 + 1) = d1 + 1 := max_self _
    apply hfold_le
    · have h0 := resYKerD1Ord_ge_tail 0 d1 k hd1 (by omega)
      have hm0 : max 0 (d1 + 1) = d1 + 1 := by omega
      rw [hm0] at h0; rw [hdp_eq]; exact h0
    · intro d0 hd0
      have hd0_le : d0 < d1 + 2 := List.mem_range.mp hd0
      have hmd : max d0 (d1 + 1) = d1 + 1 := by omega
      have h0 := resYKerD1Ord_ge_tail d0 d1 k hd1 (by omega)
      rw [hmd] at h0; rw [hdp_eq]; exact h0
  · have hne : (d0Eff == d1 + 1) = false := beq_false_of_ne heq
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact resYKerD1Ord_ge_tail d0Eff d1 k hd1 hk

/-! ### Part 2: Table 1 (`deg_R = 1` outside Table 4) pure-`Int` checker & soundness -/

/-- Exact integer certificate for one Table 1 bin `[cLo, cHi]` at `(d1, d0Eff)`.
`m = 0` means the bin is infeasible (contradiction); `m > 0` proves surplus `> δNum / δDen`
and attaches `CapWitness` `cap1` (`q₀ = 1`) and, when `cLo < 13`, `cap2` (`q₀ = 2`). -/
structure T1Cert where
  d1 : ℕ
  d0Eff : ℕ
  cLoNum : ℕ
  cLoDen : ℕ
  cHiNum : ℕ
  cHiDen : ℕ
  m : ℕ
  s : ℕ
  ua : ℕ
  vf1 : ℕ
  vlc1 : ℕ
  vres : ℕ
  vx : ℕ
  unNum : ℤ
  δNum : ℕ
  δDen : ℕ
  cap1 : CapWitness
  hasCap2 : Bool
  cap2 : CapWitness
  deriving Repr

/-- Pure-`Int` endpoint check for Table 1 at `c = cNum / cDen`:
Verifies `un_req - ua * A/N + vf1 * ((c-1)*wY + 1)/N + vlc1 * ((c-1-d1)*wY + 1)/N +
  (if d1 ≥ 2 then vres * ((d1*c + dp*(c-1-d1))*wY + dp)/N else 0) - vx * vquotLbQ(1, m, s, c)
  ≤ -vx * δNum / δDen` (strict `< 0` when `m = 0`). -/
def checkT1Endpoint (c : T1Cert) (cNum cDen : ℕ) : Bool :=
  let dp : ℕ := max c.d0Eff (c.d1 + 1)
  let hasRes : Bool := decide (2 ≤ c.d1)
  let mDen : ℤ := if c.m == 0 then 1 else (c.m : ℤ) * (c.m : ℤ)
  -- Common denominator without vquot: N * mDen * cDen
  -- Linear numerator over N * cDen (independent of m):
  let cZ : ℤ := (cNum : ℤ)
  let dZ : ℤ := (cDen : ℤ)
  let linNum : ℤ :=
    -(c.ua : ℤ) * (A : ℤ) * dZ +
    (c.vf1 : ℤ) * ((cZ - dZ) * (wY : ℤ) + dZ) +
    (c.vlc1 : ℤ) * ((cZ - (1 + (c.d1 : ℤ)) * dZ) * (wY : ℤ) + dZ) +
    if hasRes then
      (c.vres : ℤ) * (((c.d1 : ℤ) * cZ + (dp : ℤ) * (cZ - (1 + (c.d1 : ℤ)) * dZ)) * (wY : ℤ) + (dp : ℤ) * dZ)
    else 0
  if c.m == 0 then
    -- mDen = 1, vx = 0: check unNum * N * cDen + linNum < 0
    c.unNum * (N : ℤ) * dZ + linNum < 0
  else
    -- vquotLbQ = vN / (N * mDen * 8 * wY * cDen^2)
    let vN : ℤ := vquotNum 1 c.m c.s cZ dZ
    let scale : ℤ := 8 * (wY : ℤ) * dZ
    -- objNum over D = N * mDen * 8 * wY * dZ^2:
    let objNum : ℤ :=
      (c.unNum * (N : ℤ) * dZ + linNum * mDen) * scale - (c.vx : ℤ) * vN
    let D : ℤ := (N : ℤ) * mDen * scale * dZ
    -- Strict: objNum * δDen < -(vx * δNum) * D
    objNum * (c.δDen : ℤ) < -((c.vx : ℤ) * (c.δNum : ℤ) * D)

def checkT1Cert (c : T1Cert) : Bool :=
  if c.cLoDen == 0 || c.cHiDen == 0 then false
  else if !decide ((c.cLoNum : ℤ) * (c.cHiDen : ℤ) < (c.cHiNum : ℤ) * (c.cLoDen : ℤ)) then false
  else if c.m == 0 && c.vx != 0 then false
  else if c.m != 0 && (c.s < 1 || c.vx == 0 || c.δNum == 0 || c.δDen == 0) then false
  else
    let dp : ℕ := max c.d0Eff (c.d1 + 1)
    let K0 : ℕ := dp + 3
    let hasRes : Bool := decide (2 ≤ c.d1)
    let mDen : ℤ := if c.m == 0 then 1 else (c.m : ℤ) * (c.m : ℤ)
    -- Slope check: -vx * (rks[K0] - rks[K0-1]) + 2*vlc1 + (if hasRes then 2*(d1+dp)*vres else 0) ≥ 0
    let slopeNum : ℤ := rankDiffNum 1 c.m c.s K0 - rankDiffNum 1 c.m c.s (K0 - 1)
    let slopeOk : Bool :=
      (c.vx : ℤ) * slopeNum ≤
        (2 * (c.vlc1 : ℤ) + if hasRes then 2 * ((c.d1 : ℤ) + (dp : ℤ)) * (c.vres : ℤ) else 0) * mDen
    -- Pointwise check for all k ∈ 0..K0:
    let ptOk : Bool :=
      (List.range (K0 + 1)).all fun k =>
        let rkN : ℤ := rankDiffNum 1 c.m c.s k
        let h1 : ℤ := max 0 ((c.ua : ℤ) - (c.vf1 : ℤ) * ((2 * k - 1 : ℕ) : ℤ))
        let resTerm : ℤ := if hasRes then (c.vres : ℤ) * (resYKerD1Fn c.d1 c.d0Eff k : ℤ) else 0
        let lhs : ℤ :=
          (c.vx : ℤ) * rkN + (h1 - (c.vlc1 : ℤ) * ((2 * k - 1 - c.d1 : ℕ) : ℤ) - resTerm) * mDen
        lhs ≤ c.unNum
    let epOk : Bool :=
      checkT1Endpoint c c.cLoNum c.cLoDen && checkT1Endpoint c c.cHiNum c.cHiDen
    let capOk : Bool :=
      if c.m == 0 then true
      else
        checkCapWitness 1 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 1 c.cap1 &&
        (!c.hasCap2 || checkCapWitness 1 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 2 c.cap2)
    slopeOk && ptOk && epOk && capOk

/-- Soundness of `checkT1Cert`: for ANY point-order profile `k : Idx → ℕ` and bad set `Az ⊆ univ`
with `A ≤ Az.card` satisfying the three Table 1 algebraic sum bounds at `c ∈ [cLo, cHi]`:
- if `c.m = 0`, derives `False`;
- if `0 < c.m`, proves exact quotient-interpolation surplus `> δNum / δDen` AND `checkCapWitness`! -/
theorem checkT1Cert_sound (c : T1Cert) (hchk : checkT1Cert c = true)
    (cVal : ℚ) (hlo : (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ cVal)
    (hhi : cVal ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ))
    (Az : Finset Idx) (hAz : A ≤ Az.card)
    (k : Idx → ℕ)
    (hf1 : (∑ i ∈ Az, ((2 * k i - 1 : ℕ) : ℚ)) ≤ (cVal - 1) * (wY : ℚ) + 1)
    (hlc1 : (∑ i : Idx, ((2 * k i - 1 - c.d1 : ℕ) : ℚ)) ≤ (cVal - 1 - (c.d1 : ℚ)) * (wY : ℚ) + 1)
    (hres : 2 ≤ c.d1 →
      (∑ i : Idx, (resYKerD1Fn c.d1 c.d0Eff (k i) : ℚ)) ≤
        ((c.d1 : ℚ) * cVal + ((max c.d0Eff (c.d1 + 1) : ℕ) : ℚ) * (cVal - 1 - (c.d1 : ℚ))) * (wY : ℚ) +
          ((max c.d0Eff (c.d1 + 1) : ℕ) : ℚ)) :
    (c.m = 0 → False) ∧
    (0 < c.m →
      (c.δNum : ℚ) / (c.δDen : ℚ) <
        vquotLbQ 1 c.m c.s cVal - (∑ i : Idx, rankDiffQ 1 c.m c.s (k i)) / (N : ℚ) ∧
      checkCapWitness 1 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 1 c.cap1 = true ∧
      (c.hasCap2 = true → checkCapWitness 1 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 2 c.cap2 = true)) := by
  unfold checkT1Cert at hchk
  dsimp only at hchk
  by_cases h1 : (c.cLoDen == 0 || c.cHiDen == 0) = true
  · rw [if_pos h1] at hchk; cases hchk
  rw [if_neg h1] at hchk
  by_cases h2 : (!decide ((c.cLoNum : ℤ) * (c.cHiDen : ℤ) < (c.cHiNum : ℤ) * (c.cLoDen : ℤ))) = true
  · rw [if_pos h2] at hchk; cases hchk
  rw [if_neg h2] at hchk
  by_cases h3 : (c.m == 0 && c.vx != 0) = true
  · rw [if_pos h3] at hchk; cases hchk
  rw [if_neg h3] at hchk
  by_cases h4 : (c.m != 0 && (c.s < 1 || c.vx == 0 || c.δNum == 0 || c.δDen == 0)) = true
  · rw [if_pos h4] at hchk; cases hchk
  rw [if_neg h4] at hchk
  have hcLoD : 0 < c.cLoDen := by by_contra h; simp [show c.cLoDen = 0 by omega] at h1
  have hcHiD : 0 < c.cHiDen := by by_contra h; simp [show c.cHiDen = 0 by omega] at h1
  have hcltZ : (c.cLoNum : ℤ) * c.cHiDen < (c.cHiNum : ℤ) * c.cLoDen := by
    have h' : decide ((c.cLoNum : ℤ) * c.cHiDen < (c.cHiNum : ℤ) * c.cLoDen) = true := by
      cases hb : decide ((c.cLoNum : ℤ) * c.cHiDen < (c.cHiNum : ℤ) * c.cLoDen)
      · simp [hb] at h2
      · rfl
    exact decide_eq_true_eq.mp h'
  have hcLoDQ : (0 : ℚ) < (c.cLoDen : ℚ) := by exact_mod_cast hcLoD
  have hcHiDQ : (0 : ℚ) < (c.cHiDen : ℚ) := by exact_mod_cast hcHiD
  have hcltQ : (c.cLoNum : ℚ) / (c.cLoDen : ℚ) < (c.cHiNum : ℚ) / (c.cHiDen : ℚ) := by
    rw [div_lt_div_iff₀ hcLoDQ hcHiDQ]; exact_mod_cast hcltZ
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨hslope, hpt⟩, ⟨hepLo, hepHi⟩⟩, hcap⟩
  set dp : ℕ := max c.d0Eff (c.d1 + 1)
  set K0 : ℕ := dp + 3
  set mDen : ℤ := if c.m == 0 then 1 else (c.m : ℤ) * (c.m : ℤ)
  have hmDen_pos : 0 < mDen := by
    dsimp [mDen]; split_ifs with hm0
    · norm_num
    · have : 0 < c.m := Nat.pos_of_ne_zero (fun h => by simp [h] at hm0)
      positivity
  have hmDenQ : (0 : ℚ) < (mDen : ℚ) := by exact_mod_cast hmDen_pos
  have hNQ : (0 : ℚ) < (N : ℚ) := by norm_num [N]
  have hcardIdx : (Fintype.card Idx : ℚ) = (N : ℚ) := by
    have : Fintype.card Idx = N := by simp [Idx, N]
    exact_mod_cast this
  -- Step 1: Pointwise bound for EVERY k0 : ℕ (both k0 ≤ K0 and k0 > K0)!
  have hrk_eq : ∀ k0 : ℕ, (c.vx : ℚ) * ((rankDiffNum 1 c.m c.s k0 : ℚ) / (mDen : ℚ)) =
      (c.vx : ℚ) * rankDiffQ 1 c.m c.s k0 := by
    intro k0
    by_cases hm0 : c.m = 0
    · have hvx0 : c.vx = 0 := by
        by_contra hne; simp [hm0, hne] at h3
      simp [hvx0]
    · have hmpos : 0 < c.m := Nat.pos_of_ne_zero hm0
      have hmne : (c.m == 0) = false := beq_false_of_ne hm0
      have hmDen_eq : (mDen : ℚ) = (c.m : ℚ) * (c.m : ℚ) := by
        dsimp [mDen]; simp [hmne]
      rw [hmDen_eq, rankDiffNum_div_eq 1 c.m c.s k0 hmpos]
  have hpt_all : ∀ (k0 : ℕ) (α : ℚ), (α = 0 ∨ α = 1) →
      (c.vx : ℚ) * rankDiffQ 1 c.m c.s k0 + (c.ua : ℚ) * α ≤
      (c.unNum : ℚ) / (mDen : ℚ) +
      (c.vf1 : ℚ) * (α * ((2 * k0 - 1 : ℕ) : ℚ)) +
      (c.vlc1 : ℚ) * ((2 * k0 - 1 - c.d1 : ℕ) : ℚ) +
      (if 2 ≤ c.d1 then (c.vres : ℚ) * (resYKerD1Fn c.d1 c.d0Eff k0 : ℚ) else 0) := by
    have hpt_le : ∀ k0 ≤ K0,
        (c.vx : ℚ) * rankDiffQ 1 c.m c.s k0 +
        max (0 : ℚ) ((c.ua : ℚ) - (c.vf1 : ℚ) * ((2 * k0 - 1 : ℕ) : ℚ)) ≤
        (c.unNum : ℚ) / (mDen : ℚ) +
        (c.vlc1 : ℚ) * ((2 * k0 - 1 - c.d1 : ℕ) : ℚ) +
        (if 2 ≤ c.d1 then (c.vres : ℚ) * (resYKerD1Fn c.d1 c.d0Eff k0 : ℚ) else 0) := by
      intro k0 hk0
      have hmem : k0 ∈ List.range (K0 + 1) := List.mem_range.mpr (by omega)
      have hb := decide_eq_true_eq.mp (List.all_eq_true.mp hpt k0 hmem)
      have hQ : ((c.vx : ℚ) * (rankDiffNum 1 c.m c.s k0 : ℚ) +
          (max (0 : ℚ) ((c.ua : ℚ) - (c.vf1 : ℚ) * ((2 * k0 - 1 : ℕ) : ℚ)) -
            (c.vlc1 : ℚ) * ((2 * k0 - 1 - c.d1 : ℕ) : ℚ) -
            (if 2 ≤ c.d1 then (c.vres : ℚ) * (resYKerD1Fn c.d1 c.d0Eff k0 : ℚ) else 0)) * (mDen : ℚ)) ≤
          (c.unNum : ℚ) := by
        have hZ : ((c.vx : ℤ) * rankDiffNum 1 c.m c.s k0 +
            (max (0 : ℤ) ((c.ua : ℤ) - (c.vf1 : ℤ) * ((2 * k0 - 1 : ℕ) : ℤ)) -
              (c.vlc1 : ℤ) * ((2 * k0 - 1 - c.d1 : ℕ) : ℤ) -
              (if 2 ≤ c.d1 then (c.vres : ℤ) * (resYKerD1Fn c.d1 c.d0Eff k0 : ℤ) else 0)) * mDen : ℚ) ≤
            (c.unNum : ℚ) := by
          exact_mod_cast (by simpa [decide_eq_true_eq] using hb :
            (c.vx : ℤ) * rankDiffNum 1 c.m c.s k0 +
            (max (0 : ℤ) ((c.ua : ℤ) - (c.vf1 : ℤ) * ((2 * k0 - 1 : ℕ) : ℤ)) -
              (c.vlc1 : ℤ) * ((2 * k0 - 1 - c.d1 : ℕ) : ℤ) -
              (if 2 ≤ c.d1 then (c.vres : ℤ) * (resYKerD1Fn c.d1 c.d0Eff k0 : ℤ) else 0)) * mDen ≤ c.unNum)
        push_cast [Int.cast_max] at hZ
        split_ifs at hZ ⊢ <;> linarith
      rw [← hrk_eq k0]
      have hdiv := div_le_div_of_nonneg_right hQ hmDenQ.le
      rw [add_div, mul_div_assoc, mul_div_cancel_right₀ _ hmDenQ.ne'] at hdiv
      linarith
    intro k0 α hα
    have hα_max : (c.ua : ℚ) * α - (c.vf1 : ℚ) * (α * ((2 * k0 - 1 : ℕ) : ℚ)) ≤
        max (0 : ℚ) ((c.ua : ℚ) - (c.vf1 : ℚ) * ((2 * k0 - 1 : ℕ) : ℚ)) := by
      rcases hα with rfl | rfl
      · simp only [mul_zero, zero_mul, sub_zero, le_max_left]
      · simp only [mul_one, one_mul, le_max_right]
    by_cases hk0 : k0 ≤ K0
    · linarith [hpt_le k0 hk0]
    · have hgt : K0 ≤ k0 := by omega
      have hbase := hpt_le K0 le_rfl
      have hmax_mono : max (0 : ℚ) ((c.ua : ℚ) - (c.vf1 : ℚ) * ((2 * k0 - 1 : ℕ) : ℚ)) ≤
          max (0 : ℚ) ((c.ua : ℚ) - (c.vf1 : ℚ) * ((2 * K0 - 1 : ℕ) : ℚ)) := by
        apply max_le (le_max_left _ _)
        refine le_trans ?_ (le_max_right _ _)
        have h1 : ((2 * K0 - 1 : ℕ) : ℚ) ≤ ((2 * k0 - 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 2 * K0 - 1 ≤ 2 * k0 - 1)
        have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℚ) ≤ (c.vf1 : ℚ) by positivity)
        linarith only [h2]
      have htail_rk := rankDiffQ_le_linear_tail 1 c.m c.s K0 k0 (by dsimp [K0]; omega) hgt
      have hslZ := decide_eq_true_eq.mp hslope
      have hslQ : (c.vx : ℚ) * (rankDiffQ 1 c.m c.s K0 - rankDiffQ 1 c.m c.s (K0 - 1)) ≤
          2 * (c.vlc1 : ℚ) + (if 2 ≤ c.d1 then 2 * ((c.d1 : ℚ) + (dp : ℚ)) * (c.vres : ℚ) else 0) := by
        have h1 : ((c.vx : ℚ) * ((rankDiffNum 1 c.m c.s K0 : ℚ) - (rankDiffNum 1 c.m c.s (K0 - 1) : ℚ))) ≤
            (2 * (c.vlc1 : ℚ) + (if 2 ≤ c.d1 then 2 * ((c.d1 : ℚ) + (dp : ℚ)) * (c.vres : ℚ) else 0)) * (mDen : ℚ) := by
          have hZ : ((c.vx : ℤ) * (rankDiffNum 1 c.m c.s K0 - rankDiffNum 1 c.m c.s (K0 - 1)) : ℚ) ≤
              ((2 * (c.vlc1 : ℤ) + if 2 ≤ c.d1 then 2 * ((c.d1 : ℤ) + (dp : ℤ)) * (c.vres : ℤ) else 0) * mDen : ℚ) := by
            exact_mod_cast (by simpa [decide_eq_true_eq] using hslZ)
          push_cast at hZ
          split_ifs at hZ ⊢ <;> linarith
        have h2 := div_le_div_of_nonneg_right h1 hmDenQ.le
        rw [mul_div_cancel_right₀ _ hmDenQ.ne'] at h2
        have h3 : (c.vx : ℚ) * ((rankDiffNum 1 c.m c.s K0 : ℚ) - (rankDiffNum 1 c.m c.s (K0 - 1) : ℚ)) / (mDen : ℚ) =
            (c.vx : ℚ) * (rankDiffQ 1 c.m c.s K0 - rankDiffQ 1 c.m c.s (K0 - 1)) := by
          rw [mul_sub, sub_div, mul_div_assoc, mul_div_assoc, hrk_eq K0, hrk_eq (K0 - 1), ← mul_sub]
        linarith
      have hlc1_tail : ((2 * K0 - 1 - c.d1 : ℕ) : ℚ) + 2 * ((k0 - K0 : ℕ) : ℚ) ≤ ((2 * k0 - 1 - c.d1 : ℕ) : ℚ) := by
        have : (2 * K0 - 1 - c.d1) + 2 * (k0 - K0) ≤ 2 * k0 - 1 - c.d1 := by dsimp [K0, dp] at *; omega
        exact_mod_cast this
      have hres_tail : (if 2 ≤ c.d1 then (c.vres : ℚ) * (resYKerD1Fn c.d1 c.d0Eff K0 : ℚ) +
          2 * ((c.d1 : ℚ) + (dp : ℚ)) * (c.vres : ℚ) * ((k0 - K0 : ℕ) : ℚ) else 0) ≤
          (if 2 ≤ c.d1 then (c.vres : ℚ) * (resYKerD1Fn c.d1 c.d0Eff k0 : ℚ) else 0) := by
        split_ifs with hd2
        · have hfn := resYKerD1Fn_ge_tail c.d1 c.d0Eff k0 hd2 hgt
          have hfnQ : (resYKerD1Fn c.d1 c.d0Eff K0 : ℚ) +
              2 * ((c.d1 : ℚ) + (dp : ℚ)) * ((k0 - K0 : ℕ) : ℚ) ≤ (resYKerD1Fn c.d1 c.d0Eff k0 : ℚ) := by
            exact_mod_cast hfn
          have hm := mul_le_mul_of_nonneg_left hfnQ (show (0 : ℚ) ≤ (c.vres : ℚ) by positivity)
          linarith only [hm]
        · exact le_rfl
      have hstep_nn : (0 : ℚ) ≤ ((k0 - K0 : ℕ) : ℚ) := by positivity
      have hvx_nn : (0 : ℚ) ≤ (c.vx : ℚ) := by positivity
      have hvlc1_nn : (0 : ℚ) ≤ (c.vlc1 : ℚ) := by positivity
      have hrk_mul := mul_le_mul_of_nonneg_left htail_rk hvx_nn
      have hsl_mul := mul_le_mul_of_nonneg_right hslQ hstep_nn
      have hlc1_mul := mul_le_mul_of_nonneg_left hlc1_tail hvlc1_nn
      split_ifs at hbase hres_tail hsl_mul ⊢ <;>
        linarith only [hα_max, hbase, hmax_mono, hrk_mul, hsl_mul, hlc1_mul, hres_tail]
  -- Step 2: Sum hpt_all over all i : Idx and divide by N!
  have hsum_all : (c.vx : ℚ) * ((∑ i : Idx, rankDiffQ 1 c.m c.s (k i)) / (N : ℚ)) ≤
      (c.unNum : ℚ) / (mDen : ℚ) - (c.ua : ℚ) * ((A : ℚ) / (N : ℚ)) +
      (c.vf1 : ℚ) * (((cVal - 1) * (wY : ℚ) + 1) / (N : ℚ)) +
      (c.vlc1 : ℚ) * (((cVal - 1 - (c.d1 : ℚ)) * (wY : ℚ) + 1) / (N : ℚ)) +
      (if 2 ≤ c.d1 then
        (c.vres : ℚ) * ((((c.d1 : ℚ) * cVal + (dp : ℚ) * (cVal - 1 - (c.d1 : ℚ))) * (wY : ℚ) + (dp : ℚ)) / (N : ℚ))
       else 0) := by
    have hpt_i : ∀ i : Idx,
        (c.vx : ℚ) * rankDiffQ 1 c.m c.s (k i) + (c.ua : ℚ) * (if i ∈ Az then (1 : ℚ) else 0) ≤
        (c.unNum : ℚ) / (mDen : ℚ) +
        (c.vf1 : ℚ) * ((if i ∈ Az then (1 : ℚ) else 0) * ((2 * k i - 1 : ℕ) : ℚ)) +
        (c.vlc1 : ℚ) * ((2 * k i - 1 - c.d1 : ℕ) : ℚ) +
        (if 2 ≤ c.d1 then (c.vres : ℚ) * (resYKerD1Fn c.d1 c.d0Eff (k i) : ℚ) else 0) := fun i =>
      hpt_all (k i) (if i ∈ Az then 1 else 0) (by split_ifs <;> simp)
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt_i i
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hcardIdx] at hsum
    have hAz_sum : (∑ i : Idx, if i ∈ Az then (1 : ℚ) else 0) = (Az.card : ℚ) := by
      simp [Finset.sum_ite_mem]
    have hf1_sum : (∑ i : Idx, (if i ∈ Az then (1 : ℚ) else 0) * ((2 * k i - 1 : ℕ) : ℚ)) =
        ∑ i ∈ Az, ((2 * k i - 1 : ℕ) : ℚ) := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    rw [hAz_sum, hf1_sum] at hsum
    have hAzQ : (A : ℚ) ≤ (Az.card : ℚ) := by exact_mod_cast hAz
    have hres_sum : (∑ i : Idx, if 2 ≤ c.d1 then (c.vres : ℚ) * (resYKerD1Fn c.d1 c.d0Eff (k i) : ℚ) else 0) ≤
        (if 2 ≤ c.d1 then (c.vres : ℚ) * (((c.d1 : ℚ) * cVal + (dp : ℚ) * (cVal - 1 - (c.d1 : ℚ))) * (wY : ℚ) + (dp : ℚ)) else 0) := by
      split_ifs with hd2
      · rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hres hd2) (by positivity)
      · simp
    have hcomb : (c.vx : ℚ) * (∑ i : Idx, rankDiffQ 1 c.m c.s (k i)) ≤
        (N : ℚ) * ((c.unNum : ℚ) / (mDen : ℚ)) - (c.ua : ℚ) * (A : ℚ) +
        (c.vf1 : ℚ) * ((cVal - 1) * (wY : ℚ) + 1) +
        (c.vlc1 : ℚ) * ((cVal - 1 - (c.d1 : ℚ)) * (wY : ℚ) + 1) +
        (if 2 ≤ c.d1 then (c.vres : ℚ) * (((c.d1 : ℚ) * cVal + (dp : ℚ) * (cVal - 1 - (c.d1 : ℚ))) * (wY : ℚ) + (dp : ℚ)) else 0) := by
      have ha := mul_le_mul_of_nonneg_left hAzQ (show (0 : ℚ) ≤ (c.ua : ℚ) by positivity)
      have hb := mul_le_mul_of_nonneg_left hf1 (show (0 : ℚ) ≤ (c.vf1 : ℚ) by positivity)
      have hc := mul_le_mul_of_nonneg_left hlc1 (show (0 : ℚ) ≤ (c.vlc1 : ℚ) by positivity)
      linarith only [hsum, hres_sum, ha, hb, hc]
    have hdiv := div_le_div_of_nonneg_right hcomb hNQ.le
    rw [mul_div_assoc] at hdiv
    refine hdiv.trans ?_
    split_ifs <;> (field_simp [hNQ.ne']; linarith)
  -- Step 3: Decode BOTH endpoint checks + affine/concave interpolation to cVal!
  let L (x : ℚ) : ℚ :=
    (c.unNum : ℚ) / (mDen : ℚ) - (c.ua : ℚ) * ((A : ℚ) / (N : ℚ)) +
    (c.vf1 : ℚ) * (((x - 1) * (wY : ℚ) + 1) / (N : ℚ)) +
    (c.vlc1 : ℚ) * (((x - 1 - (c.d1 : ℚ)) * (wY : ℚ) + 1) / (N : ℚ)) +
    (if 2 ≤ c.d1 then
      (c.vres : ℚ) * ((((c.d1 : ℚ) * x + (dp : ℚ) * (x - 1 - (c.d1 : ℚ))) * (wY : ℚ) + (dp : ℚ)) / (N : ℚ))
     else 0)
  have hL_affine : ∀ (x y t : ℚ), L ((1 - t) * x + t * y) = (1 - t) * L x + t * L y := by
    intro x y t; dsimp only [L]; split_ifs <;> ring
  set t : ℚ := (cVal - (c.cLoNum : ℚ) / (c.cLoDen : ℚ)) /
      ((c.cHiNum : ℚ) / (c.cHiDen : ℚ) - (c.cLoNum : ℚ) / (c.cLoDen : ℚ))
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) (sub_pos.mpr hcltQ).le
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hcltQ)).mpr (sub_le_sub_right hhi _)
  have hcVal_eq : cVal = (1 - t) * ((c.cLoNum : ℚ) / (c.cLoDen : ℚ)) + t * ((c.cHiNum : ℚ) / (c.cHiDen : ℚ)) :=
    linear_interp_eq hcltQ
  have hL_ep : ∀ (cNum cDen : ℕ) (hcD : 0 < cDen), checkT1Endpoint c cNum cDen = true →
      (c.m = 0 → L ((cNum : ℚ) / (cDen : ℚ)) < 0) ∧
      (0 < c.m → L ((cNum : ℚ) / (cDen : ℚ)) - (c.vx : ℚ) * vquotLbQ 1 c.m c.s ((cNum : ℚ) / (cDen : ℚ)) <
        -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ))) := by
    intro cNum cDen hcD hep
    have hcDQ : (0 : ℚ) < (cDen : ℚ) := by exact_mod_cast hcD
    have hwYQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY, D]
    unfold checkT1Endpoint at hep
    dsimp only at hep
    set linZ : ℤ :=
      -(c.ua : ℤ) * (A : ℤ) * (cDen : ℤ) +
      (c.vf1 : ℤ) * (((cNum : ℤ) - (cDen : ℤ)) * (wY : ℤ) + (cDen : ℤ)) +
      (c.vlc1 : ℤ) * (((cNum : ℤ) - (1 + (c.d1 : ℤ)) * (cDen : ℤ)) * (wY : ℤ) + (cDen : ℤ)) +
      if 2 ≤ c.d1 then
        (c.vres : ℤ) * ((((c.d1 : ℤ) * (cNum : ℤ) + (dp : ℤ) * ((cNum : ℤ) - (1 + (c.d1 : ℤ)) * (cDen : ℤ))) * (wY : ℤ) + (dp : ℤ) * (cDen : ℤ)))
      else 0
    have hL_eq : L ((cNum : ℚ) / (cDen : ℚ)) =
        ((c.unNum : ℚ) * (N : ℚ) * (cDen : ℚ) + (linZ : ℚ) * (mDen : ℚ)) / ((N : ℚ) * (mDen : ℚ) * (cDen : ℚ)) := by
      dsimp only [L, linZ]
      split_ifs <;> (push_cast; field_simp [hNQ.ne', hmDenQ.ne', hcDQ.ne']; ring)
    constructor
    · intro hm0
      have hm0b : (c.m == 0) = true := beq_iff_eq.mpr hm0
      rw [if_pos hm0b] at hep
      have hZ : c.unNum * (N : ℤ) * (cDen : ℤ) + linZ < 0 := by
        simpa [linZ, dp, decide_eq_true_eq] using decide_eq_true_eq.mp hep
      have hm1 : (mDen : ℚ) = 1 := by dsimp [mDen]; simp [hm0b]
      rw [hL_eq, hm1, mul_one, mul_one]
      exact div_neg_of_neg_of_pos (by exact_mod_cast hZ) (by positivity)
    · intro hmpos
      have hm0b : (c.m == 0) = false := beq_false_of_ne (Nat.ne_of_gt hmpos)
      rw [if_neg (by simp [hm0b])] at hep
      have hδD : 0 < c.δDen := by by_contra h; simp [Nat.ne_of_gt hmpos, show c.δDen = 0 by omega] at h4
      have hδDQ : (0 : ℚ) < (c.δDen : ℚ) := by exact_mod_cast hδD
      have hZ := decide_eq_true_eq.mp hep
      have hv := vquotNum_div_eq 1 c.m c.s hmpos cNum cDen (by exact_mod_cast hcD)
      simp only [Int.cast_natCast] at hv
      have hmDen_eq : (mDen : ℚ) = (c.m : ℚ) * (c.m : ℚ) := by dsimp [mDen]; simp [hm0b]
      have hvD_eq : (vquotDen c.m cDen : ℚ) = (N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (cDen : ℚ) := by
        unfold vquotDen; rw [hmDen_eq]; push_cast; ring
      have hsub_eq : L ((cNum : ℚ) / (cDen : ℚ)) - (c.vx : ℚ) * vquotLbQ 1 c.m c.s ((cNum : ℚ) / (cDen : ℚ)) =
          (((c.unNum : ℚ) * (N : ℚ) * (cDen : ℚ) + (linZ : ℚ) * (mDen : ℚ)) * (8 * (wY : ℚ) * (cDen : ℚ)) -
            (c.vx : ℚ) * (vquotNum 1 c.m c.s cNum cDen : ℚ)) /
          ((N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (cDen : ℚ)) := by
        rw [hL_eq, ← hv, hvD_eq]
        field_simp [hNQ.ne', hmDenQ.ne', hcDQ.ne', hwYQ.ne']
      rw [hsub_eq]
      have hDpos : (0 : ℚ) < (N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (cDen : ℚ) := by positivity
      rw [show -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) = -((c.vx : ℚ) * (c.δNum : ℚ)) / (c.δDen : ℚ) by ring]
      rw [div_lt_div_iff₀ hDpos hδDQ]
      have hQ : (((c.unNum : ℤ) * (N : ℤ) * (cDen : ℤ) + linZ * mDen) * (8 * (wY : ℤ) * (cDen : ℤ)) -
          (c.vx : ℤ) * vquotNum 1 c.m c.s cNum cDen : ℚ) * (c.δDen : ℚ) <
          -((c.vx : ℚ) * (c.δNum : ℚ) * ((N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (cDen : ℚ))) := by
        have hZ' : ((c.unNum * (N : ℤ) * (cDen : ℤ) + linZ * mDen) * (8 * (wY : ℤ) * (cDen : ℤ)) -
            (c.vx : ℤ) * vquotNum 1 c.m c.s cNum cDen) * (c.δDen : ℤ) <
            -((c.vx : ℤ) * (c.δNum : ℤ) * ((N : ℤ) * mDen * (8 * (wY : ℤ) * (cDen : ℤ)) * (cDen : ℤ))) := by
          simpa [linZ, dp, mDen, hm0b, decide_eq_true_eq] using hZ
        exact_mod_cast hZ'
      push_cast at hQ; linarith
  have hLo := hL_ep c.cLoNum c.cLoDen hcLoD hepLo
  have hHi := hL_ep c.cHiNum c.cHiDen hcHiD hepHi
  constructor
  · intro hm0
    have hvx0 : c.vx = 0 := by by_contra hne; simp [hm0, hne] at h3
    have hL_lt : L cVal < 0 := by
      rw [hcVal_eq, hL_affine]; exact convex_comb_lt ht0 ht1 (hLo.1 hm0) (hHi.1 hm0)
    have h0le : (0 : ℚ) ≤ L cVal := by simpa [hvx0, L] using hsum_all
    linarith
  · intro hmpos
    have hm0b : (c.m == 0) = false := beq_false_of_ne (Nat.ne_of_gt hmpos)
    have hvxpos : 0 < c.vx := by by_contra h; simp [Nat.ne_of_gt hmpos, show c.vx = 0 by omega] at h4
    have hvxQ : (0 : ℚ) < (c.vx : ℚ) := by exact_mod_cast hvxpos
    have hsec := vquotLbQ_ge_secant 1 c.m c.s hmpos hlo hhi hcltQ
    have hL_lt : L cVal - (c.vx : ℚ) * vquotLbQ 1 c.m c.s cVal < -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) := by
      have hlin : (1 - t) * (L ((c.cLoNum : ℚ) / (c.cLoDen : ℚ)) - (c.vx : ℚ) * vquotLbQ 1 c.m c.s ((c.cLoNum : ℚ) / (c.cLoDen : ℚ))) +
          t * (L ((c.cHiNum : ℚ) / (c.cHiDen : ℚ)) - (c.vx : ℚ) * vquotLbQ 1 c.m c.s ((c.cHiNum : ℚ) / (c.cHiDen : ℚ))) <
          -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) :=
        convex_comb_lt ht0 ht1 (hLo.2 hmpos) (hHi.2 hmpos)
      have hL_c : L cVal = (1 - t) * L ((c.cLoNum : ℚ) / (c.cLoDen : ℚ)) + t * L ((c.cHiNum : ℚ) / (c.cHiDen : ℚ)) := by
        rw [← hL_affine, ← hcVal_eq]
      have hsec_m := mul_le_mul_of_nonneg_left hsec hvxQ.le
      linarith only [hlin, hL_c, hsec_m]
    have hsurp : (c.δNum : ℚ) / (c.δDen : ℚ) <
        vquotLbQ 1 c.m c.s cVal - (∑ i : Idx, rankDiffQ 1 c.m c.s (k i)) / (N : ℚ) := by
      have h1 : (c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) <
          (c.vx : ℚ) * (vquotLbQ 1 c.m c.s cVal - (∑ i : Idx, rankDiffQ 1 c.m c.s (k i)) / (N : ℚ)) := by
        dsimp only [L] at hL_lt; linarith only [hL_lt, hsum_all]
      exact lt_of_mul_lt_mul_left h1 hvxQ.le
    rw [if_neg (by simp [hm0b])] at hcap
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hcap
    refine ⟨hsurp, hcap.1, fun h2 => ?_⟩
    rcases hcap.2 with hno | hok
    · rw [h2] at hno; cases hno
    · exact hok

/-! ### Part 3: Table 2 (`deg_R = 2`, `gcd(f_1, f_2) = 1`) pure-`Int` checker & soundness -/

structure T2Cert where
  d1 : ℕ
  d2 : ℕ
  cLoNum : ℕ
  cLoDen : ℕ
  cHiNum : ℕ
  cHiDen : ℕ
  m : ℕ
  s : ℕ
  ua : ℕ
  vf1 : ℕ
  vf2 : ℕ
  vlc1 : ℕ
  vlc2 : ℕ
  vres : ℕ
  vx : ℕ
  unNum : ℤ
  δNum : ℕ
  δDen : ℕ
  cap : CapWitness
  deriving Repr

def checkT2Endpoint (c : T2Cert) (cNum cDen : ℕ) : Bool :=
  let hasRes : Bool := decide (1 ≤ c.d1 ∧ 2 ≤ c.d2)
  let mDen : ℤ := if c.m == 0 then 1 else (c.m : ℤ) * (c.m : ℤ)
  let cZ : ℤ := (cNum : ℤ)
  let dZ : ℤ := (cDen : ℤ)
  let d1Z : ℤ := (c.d1 : ℤ)
  let d2Z : ℤ := (c.d2 : ℤ)
  let linNum : ℤ :=
    -(c.ua : ℤ) * (A : ℤ) * dZ +
    (c.vf1 : ℤ) * ((cZ - dZ) * (wY : ℤ) + dZ) +
    (c.vf2 : ℤ) * ((cZ - 2 * dZ) * (wY : ℤ) + 2 * dZ) +
    (c.vlc1 : ℤ) * ((cZ - (1 + d1Z) * dZ) * (wY : ℤ) + dZ) +
    (c.vlc2 : ℤ) * ((cZ - (2 + d2Z) * dZ) * (wY : ℤ) + 2 * dZ) +
    if hasRes then
      (c.vres : ℤ) * ((d2Z * (cZ - dZ) + d1Z * (cZ - 2 * dZ) - d1Z * d2Z * dZ) * (wY : ℤ) + (d2Z + 2 * d1Z) * dZ)
    else 0
  if c.m == 0 then
    c.unNum * (N : ℤ) * dZ + linNum < 0
  else
    let vN : ℤ := vquotNum 2 c.m c.s cZ dZ
    let scale : ℤ := 8 * (wY : ℤ) * dZ
    let objNum : ℤ := (c.unNum * (N : ℤ) * dZ + linNum * mDen) * scale - (c.vx : ℤ) * vN
    let D : ℤ := (N : ℤ) * mDen * scale * dZ
    objNum * (c.δDen : ℤ) < -((c.vx : ℤ) * (c.δNum : ℤ) * D)

def checkT2Cert (c : T2Cert) : Bool :=
  if c.cLoDen == 0 || c.cHiDen == 0 then false
  else if !decide ((c.cLoNum : ℤ) * (c.cHiDen : ℤ) < (c.cHiNum : ℤ) * (c.cLoDen : ℤ)) then false
  else if c.m == 0 && c.vx != 0 then false
  else if c.m != 0 && (c.s < 2 || c.vx == 0 || c.δNum == 0 || c.δDen == 0) then false
  else
    let K0 : ℕ := max c.d1 c.d2 + 3
    let hasRes : Bool := decide (1 ≤ c.d1 ∧ 2 ≤ c.d2)
    let mDen : ℤ := if c.m == 0 then 1 else (c.m : ℤ) * (c.m : ℤ)
    let slopeNum : ℤ := rankDiffNum 2 c.m c.s K0 - rankDiffNum 2 c.m c.s (K0 - 1)
    let slopeOk : Bool :=
      (c.vx : ℤ) * slopeNum ≤
        (2 * (c.vlc1 : ℤ) + 2 * (c.vlc2 : ℤ) +
          if hasRes then 2 * ((c.d1 : ℤ) + (c.d2 : ℤ)) * (c.vres : ℤ) else 0) * mDen
    let ptOk : Bool :=
      (List.range (K0 + 1)).all fun k =>
        let rkN : ℤ := rankDiffNum 2 c.m c.s k
        let h1 : ℤ := max 0 ((c.ua : ℤ) - (c.vf1 : ℤ) * ((2 * k - 1 : ℕ) : ℤ) - (c.vf2 : ℤ) * ((2 * k - 2 : ℕ) : ℤ))
        let resTerm : ℤ := if hasRes then (c.vres : ℤ) * (resOrdExact c.d1 (2 * k - 1) c.d2 (2 * k - 2) : ℤ) else 0
        let lhs : ℤ :=
          (c.vx : ℤ) * rkN +
            (h1 - (c.vlc1 : ℤ) * ((2 * k - 1 - c.d1 : ℕ) : ℤ) -
              (c.vlc2 : ℤ) * ((2 * k - 2 - c.d2 : ℕ) : ℤ) - resTerm) * mDen
        lhs ≤ c.unNum
    let epOk : Bool :=
      checkT2Endpoint c c.cLoNum c.cLoDen && checkT2Endpoint c c.cHiNum c.cHiDen
    let capOk : Bool :=
      if c.m == 0 then true
      else checkCapWitness 2 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 1 c.cap
    slopeOk && ptOk && epOk && capOk

theorem checkT2Cert_sound (c : T2Cert) (hchk : checkT2Cert c = true)
    (cVal : ℚ) (hlo : (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ cVal)
    (hhi : cVal ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ))
    (Az : Finset Idx) (hAz : A ≤ Az.card)
    (k : Idx → ℕ)
    (hf1 : (∑ i ∈ Az, ((2 * k i - 1 : ℕ) : ℚ)) ≤ (cVal - 1) * (wY : ℚ) + 1)
    (hf2 : (∑ i ∈ Az, ((2 * k i - 2 : ℕ) : ℚ)) ≤ (cVal - 2) * (wY : ℚ) + 2)
    (hlc1 : (∑ i : Idx, ((2 * k i - 1 - c.d1 : ℕ) : ℚ)) ≤ (cVal - 1 - (c.d1 : ℚ)) * (wY : ℚ) + 1)
    (hlc2 : (∑ i : Idx, ((2 * k i - 2 - c.d2 : ℕ) : ℚ)) ≤ (cVal - 2 - (c.d2 : ℚ)) * (wY : ℚ) + 2)
    (hres : 1 ≤ c.d1 ∧ 2 ≤ c.d2 →
      (∑ i : Idx, (resOrdExact c.d1 (2 * k i - 1) c.d2 (2 * k i - 2) : ℚ)) ≤
        ((c.d2 : ℚ) * (cVal - 1) + (c.d1 : ℚ) * (cVal - 2) - (c.d1 : ℚ) * (c.d2 : ℚ)) * (wY : ℚ) +
          ((c.d2 : ℚ) + 2 * (c.d1 : ℚ))) :
    (c.m = 0 → False) ∧
    (0 < c.m →
      (c.δNum : ℚ) / (c.δDen : ℚ) <
        vquotLbQ 2 c.m c.s cVal - (∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) / (N : ℚ) ∧
      checkCapWitness 2 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 1 c.cap = true) := by
  unfold checkT2Cert at hchk
  dsimp only at hchk
  by_cases h1 : (c.cLoDen == 0 || c.cHiDen == 0) = true
  · rw [if_pos h1] at hchk; cases hchk
  rw [if_neg h1] at hchk
  by_cases h2 : (!decide ((c.cLoNum : ℤ) * (c.cHiDen : ℤ) < (c.cHiNum : ℤ) * (c.cLoDen : ℤ))) = true
  · rw [if_pos h2] at hchk; cases hchk
  rw [if_neg h2] at hchk
  by_cases h3 : (c.m == 0 && c.vx != 0) = true
  · rw [if_pos h3] at hchk; cases hchk
  rw [if_neg h3] at hchk
  by_cases h4 : (c.m != 0 && (c.s < 2 || c.vx == 0 || c.δNum == 0 || c.δDen == 0)) = true
  · rw [if_pos h4] at hchk; cases hchk
  rw [if_neg h4] at hchk
  have hcLoD : 0 < c.cLoDen := by by_contra h; simp [show c.cLoDen = 0 by omega] at h1
  have hcHiD : 0 < c.cHiDen := by by_contra h; simp [show c.cHiDen = 0 by omega] at h1
  have hcltZ : (c.cLoNum : ℤ) * c.cHiDen < (c.cHiNum : ℤ) * c.cLoDen := by
    have h' : decide ((c.cLoNum : ℤ) * c.cHiDen < (c.cHiNum : ℤ) * c.cLoDen) = true := by
      cases hb : decide ((c.cLoNum : ℤ) * c.cHiDen < (c.cHiNum : ℤ) * c.cLoDen)
      · simp [hb] at h2
      · rfl
    exact decide_eq_true_eq.mp h'
  have hcLoDQ : (0 : ℚ) < (c.cLoDen : ℚ) := by exact_mod_cast hcLoD
  have hcHiDQ : (0 : ℚ) < (c.cHiDen : ℚ) := by exact_mod_cast hcHiD
  have hcltQ : (c.cLoNum : ℚ) / (c.cLoDen : ℚ) < (c.cHiNum : ℚ) / (c.cHiDen : ℚ) := by
    rw [div_lt_div_iff₀ hcLoDQ hcHiDQ]; exact_mod_cast hcltZ
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨hslope, hpt⟩, ⟨hepLo, hepHi⟩⟩, hcap⟩
  set K0 : ℕ := max c.d1 c.d2 + 3
  set mDen : ℤ := if c.m == 0 then 1 else (c.m : ℤ) * (c.m : ℤ)
  have hmDen_pos : 0 < mDen := by
    dsimp [mDen]; split_ifs with hm0
    · norm_num
    · have : 0 < c.m := Nat.pos_of_ne_zero (fun h => by simp [h] at hm0); positivity
  have hmDenQ : (0 : ℚ) < (mDen : ℚ) := by exact_mod_cast hmDen_pos
  have hNQ : (0 : ℚ) < (N : ℚ) := by norm_num [N]
  have hcardIdx : (Fintype.card Idx : ℚ) = (N : ℚ) := by
    have : Fintype.card Idx = N := by simp [Idx, N]
    exact_mod_cast this
  have hrk_eq : ∀ k0 : ℕ, (c.vx : ℚ) * ((rankDiffNum 2 c.m c.s k0 : ℚ) / (mDen : ℚ)) =
      (c.vx : ℚ) * rankDiffQ 2 c.m c.s k0 := by
    intro k0
    by_cases hm0 : c.m = 0
    · have hvx0 : c.vx = 0 := by by_contra hne; simp [hm0, hne] at h3
      simp [hvx0]
    · have hmpos : 0 < c.m := Nat.pos_of_ne_zero hm0
      have hmne : (c.m == 0) = false := beq_false_of_ne hm0
      have hmDen_eq : (mDen : ℚ) = (c.m : ℚ) * (c.m : ℚ) := by dsimp [mDen]; simp [hmne]
      rw [hmDen_eq, rankDiffNum_div_eq 2 c.m c.s k0 hmpos]
  have hpt_all : ∀ (k0 : ℕ) (α : ℚ), (α = 0 ∨ α = 1) →
      (c.vx : ℚ) * rankDiffQ 2 c.m c.s k0 + (c.ua : ℚ) * α ≤
      (c.unNum : ℚ) / (mDen : ℚ) +
      (c.vf1 : ℚ) * (α * ((2 * k0 - 1 : ℕ) : ℚ)) +
      (c.vf2 : ℚ) * (α * ((2 * k0 - 2 : ℕ) : ℚ)) +
      (c.vlc1 : ℚ) * ((2 * k0 - 1 - c.d1 : ℕ) : ℚ) +
      (c.vlc2 : ℚ) * ((2 * k0 - 2 - c.d2 : ℕ) : ℚ) +
      (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then (c.vres : ℚ) * (resOrdExact c.d1 (2 * k0 - 1) c.d2 (2 * k0 - 2) : ℚ) else 0) := by
    have hpt_le : ∀ k0 ≤ K0,
        (c.vx : ℚ) * rankDiffQ 2 c.m c.s k0 +
        max (0 : ℚ) ((c.ua : ℚ) - (c.vf1 : ℚ) * ((2 * k0 - 1 : ℕ) : ℚ) - (c.vf2 : ℚ) * ((2 * k0 - 2 : ℕ) : ℚ)) ≤
        (c.unNum : ℚ) / (mDen : ℚ) +
        (c.vlc1 : ℚ) * ((2 * k0 - 1 - c.d1 : ℕ) : ℚ) +
        (c.vlc2 : ℚ) * ((2 * k0 - 2 - c.d2 : ℕ) : ℚ) +
        (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then (c.vres : ℚ) * (resOrdExact c.d1 (2 * k0 - 1) c.d2 (2 * k0 - 2) : ℚ) else 0) := by
      intro k0 hk0
      have hmem : k0 ∈ List.range (K0 + 1) := List.mem_range.mpr (by omega)
      have hb := decide_eq_true_eq.mp (List.all_eq_true.mp hpt k0 hmem)
      have hQ : ((c.vx : ℚ) * (rankDiffNum 2 c.m c.s k0 : ℚ) +
          (max (0 : ℚ) ((c.ua : ℚ) - (c.vf1 : ℚ) * ((2 * k0 - 1 : ℕ) : ℚ) - (c.vf2 : ℚ) * ((2 * k0 - 2 : ℕ) : ℚ)) -
            (c.vlc1 : ℚ) * ((2 * k0 - 1 - c.d1 : ℕ) : ℚ) -
            (c.vlc2 : ℚ) * ((2 * k0 - 2 - c.d2 : ℕ) : ℚ) -
            (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then (c.vres : ℚ) * (resOrdExact c.d1 (2 * k0 - 1) c.d2 (2 * k0 - 2) : ℚ) else 0)) * (mDen : ℚ)) ≤
          (c.unNum : ℚ) := by
        have hZ : ((c.vx : ℤ) * rankDiffNum 2 c.m c.s k0 +
            (max (0 : ℤ) ((c.ua : ℤ) - (c.vf1 : ℤ) * ((2 * k0 - 1 : ℕ) : ℤ) - (c.vf2 : ℤ) * ((2 * k0 - 2 : ℕ) : ℤ)) -
              (c.vlc1 : ℤ) * ((2 * k0 - 1 - c.d1 : ℕ) : ℤ) -
              (c.vlc2 : ℤ) * ((2 * k0 - 2 - c.d2 : ℕ) : ℤ) -
              (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then (c.vres : ℤ) * (resOrdExact c.d1 (2 * k0 - 1) c.d2 (2 * k0 - 2) : ℤ) else 0)) * mDen : ℚ) ≤
            (c.unNum : ℚ) := by
          exact_mod_cast (by simpa [decide_eq_true_eq] using hb :
            (c.vx : ℤ) * rankDiffNum 2 c.m c.s k0 +
            (max (0 : ℤ) ((c.ua : ℤ) - (c.vf1 : ℤ) * ((2 * k0 - 1 : ℕ) : ℤ) - (c.vf2 : ℤ) * ((2 * k0 - 2 : ℕ) : ℤ)) -
              (c.vlc1 : ℤ) * ((2 * k0 - 1 - c.d1 : ℕ) : ℤ) -
              (c.vlc2 : ℤ) * ((2 * k0 - 2 - c.d2 : ℕ) : ℤ) -
              (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then (c.vres : ℤ) * (resOrdExact c.d1 (2 * k0 - 1) c.d2 (2 * k0 - 2) : ℤ) else 0)) * mDen ≤ c.unNum)
        push_cast [Int.cast_max] at hZ
        split_ifs at hZ ⊢ <;> linarith
      rw [← hrk_eq k0]
      have hdiv := div_le_div_of_nonneg_right hQ hmDenQ.le
      rw [add_div, mul_div_assoc, mul_div_cancel_right₀ _ hmDenQ.ne'] at hdiv
      linarith
    intro k0 α hα
    have hα_max : (c.ua : ℚ) * α - (c.vf1 : ℚ) * (α * ((2 * k0 - 1 : ℕ) : ℚ)) - (c.vf2 : ℚ) * (α * ((2 * k0 - 2 : ℕ) : ℚ)) ≤
        max (0 : ℚ) ((c.ua : ℚ) - (c.vf1 : ℚ) * ((2 * k0 - 1 : ℕ) : ℚ) - (c.vf2 : ℚ) * ((2 * k0 - 2 : ℕ) : ℚ)) := by
      rcases hα with rfl | rfl
      · simp only [mul_zero, zero_mul, sub_zero, le_max_left]
      · simp only [mul_one, one_mul, le_max_right]
    by_cases hk0 : k0 ≤ K0
    · linarith [hpt_le k0 hk0]
    · have hgt : K0 ≤ k0 := by omega
      have hbase := hpt_le K0 le_rfl
      have hmax_mono : max (0 : ℚ) ((c.ua : ℚ) - (c.vf1 : ℚ) * ((2 * k0 - 1 : ℕ) : ℚ) - (c.vf2 : ℚ) * ((2 * k0 - 2 : ℕ) : ℚ)) ≤
          max (0 : ℚ) ((c.ua : ℚ) - (c.vf1 : ℚ) * ((2 * K0 - 1 : ℕ) : ℚ) - (c.vf2 : ℚ) * ((2 * K0 - 2 : ℕ) : ℚ)) := by
        apply max_le (le_max_left _ _)
        refine le_trans ?_ (le_max_right _ _)
        have h1 : ((2 * K0 - 1 : ℕ) : ℚ) ≤ ((2 * k0 - 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 2 * K0 - 1 ≤ 2 * k0 - 1)
        have h2 : ((2 * K0 - 2 : ℕ) : ℚ) ≤ ((2 * k0 - 2 : ℕ) : ℚ) := by exact_mod_cast (by omega : 2 * K0 - 2 ≤ 2 * k0 - 2)
        have hm1 := mul_le_mul_of_nonneg_left h1 (show (0 : ℚ) ≤ (c.vf1 : ℚ) by positivity)
        have hm2 := mul_le_mul_of_nonneg_left h2 (show (0 : ℚ) ≤ (c.vf2 : ℚ) by positivity)
        linarith only [hm1, hm2]
      have htail_rk := rankDiffQ_le_linear_tail 2 c.m c.s K0 k0 (by dsimp [K0]; omega) hgt
      have hslZ := decide_eq_true_eq.mp hslope
      have hslQ : (c.vx : ℚ) * (rankDiffQ 2 c.m c.s K0 - rankDiffQ 2 c.m c.s (K0 - 1)) ≤
          2 * (c.vlc1 : ℚ) + 2 * (c.vlc2 : ℚ) +
          (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then 2 * ((c.d1 : ℚ) + (c.d2 : ℚ)) * (c.vres : ℚ) else 0) := by
        have h1 : ((c.vx : ℚ) * ((rankDiffNum 2 c.m c.s K0 : ℚ) - (rankDiffNum 2 c.m c.s (K0 - 1) : ℚ))) ≤
            (2 * (c.vlc1 : ℚ) + 2 * (c.vlc2 : ℚ) +
              (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then 2 * ((c.d1 : ℚ) + (c.d2 : ℚ)) * (c.vres : ℚ) else 0)) * (mDen : ℚ) := by
          have hZ : ((c.vx : ℤ) * (rankDiffNum 2 c.m c.s K0 - rankDiffNum 2 c.m c.s (K0 - 1)) : ℚ) ≤
              ((2 * (c.vlc1 : ℤ) + 2 * (c.vlc2 : ℤ) +
                if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then 2 * ((c.d1 : ℤ) + (c.d2 : ℤ)) * (c.vres : ℤ) else 0) * mDen : ℚ) := by
            exact_mod_cast (by simpa [decide_eq_true_eq] using hslZ)
          push_cast at hZ
          split_ifs at hZ ⊢ <;> linarith
        have h2 := div_le_div_of_nonneg_right h1 hmDenQ.le
        rw [mul_div_cancel_right₀ _ hmDenQ.ne'] at h2
        have h3 : (c.vx : ℚ) * ((rankDiffNum 2 c.m c.s K0 : ℚ) - (rankDiffNum 2 c.m c.s (K0 - 1) : ℚ)) / (mDen : ℚ) =
            (c.vx : ℚ) * (rankDiffQ 2 c.m c.s K0 - rankDiffQ 2 c.m c.s (K0 - 1)) := by
          rw [mul_sub, sub_div, mul_div_assoc, mul_div_assoc, hrk_eq K0, hrk_eq (K0 - 1), ← mul_sub]
        linarith
      have hlc1_t : ((2 * K0 - 1 - c.d1 : ℕ) : ℚ) + 2 * ((k0 - K0 : ℕ) : ℚ) ≤ ((2 * k0 - 1 - c.d1 : ℕ) : ℚ) := by
        exact_mod_cast (by dsimp [K0] at *; omega : (2 * K0 - 1 - c.d1) + 2 * (k0 - K0) ≤ 2 * k0 - 1 - c.d1)
      have hlc2_t : ((2 * K0 - 2 - c.d2 : ℕ) : ℚ) + 2 * ((k0 - K0 : ℕ) : ℚ) ≤ ((2 * k0 - 2 - c.d2 : ℕ) : ℚ) := by
        exact_mod_cast (by dsimp [K0] at *; omega : (2 * K0 - 2 - c.d2) + 2 * (k0 - K0) ≤ 2 * k0 - 2 - c.d2)
      have hres_t : (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then
          (c.vres : ℚ) * (resOrdExact c.d1 (2 * K0 - 1) c.d2 (2 * K0 - 2) : ℚ) +
          2 * ((c.d1 : ℚ) + (c.d2 : ℚ)) * (c.vres : ℚ) * ((k0 - K0 : ℕ) : ℚ) else 0) ≤
          (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then (c.vres : ℚ) * (resOrdExact c.d1 (2 * k0 - 1) c.d2 (2 * k0 - 2) : ℚ) else 0) := by
        split_ifs with hr
        · have hre : resOrdExact c.d1 (2 * K0 - 1) c.d2 (2 * K0 - 2) + 2 * (c.d1 + c.d2) * (k0 - K0) ≤
              resOrdExact c.d1 (2 * k0 - 1) c.d2 (2 * k0 - 2) := by
            unfold resOrdExact
            have hd1ne : c.d1 ≠ 0 := by omega
            have hd2ne : c.d2 ≠ 0 := by omega
            simp only [hd1ne, hd2ne, ↓reduceIte]
            have hza : c.d1 - (2 * K0 - 1) = 0 := by dsimp [K0]; omega
            have hzb : c.d2 - (2 * K0 - 2) = 0 := by dsimp [K0]; omega
            have hzc : c.d1 - (2 * k0 - 1) = 0 := by dsimp [K0] at hgt; omega
            have hzd : c.d2 - (2 * k0 - 2) = 0 := by dsimp [K0] at hgt; omega
            rw [hza, hzb, hzc, hzd, Nat.zero_mul, Nat.add_zero, Nat.add_zero]
            have hK1 : c.d1 ≤ 2 * K0 - 2 := by dsimp [K0]; omega
            have hK2 : c.d2 ≤ 2 * K0 - 2 := by dsimp [K0]; omega
            have hk1 : c.d1 ≤ 2 * k0 - 2 := by omega
            have hk2 : c.d2 ≤ 2 * k0 - 2 := by omega
            have hle1 : c.d1 * c.d2 ≤ c.d2 * (2 * K0 - 1) + c.d1 * (2 * K0 - 2) := by nlinarith only [hK1, hK2]
            have hle2 : c.d1 * c.d2 ≤ c.d2 * (2 * k0 - 1) + c.d1 * (2 * k0 - 2) := by nlinarith only [hk1, hk2]
            have hK0_le : K0 ≤ k0 := hgt
            zify [hle1, hle2, hK0_le, show 1 ≤ 2 * K0 by dsimp [K0]; omega,
              show 1 ≤ 2 * k0 by dsimp [K0] at hgt; omega,
              show 2 ≤ 2 * K0 by dsimp [K0]; omega, show 2 ≤ 2 * k0 by dsimp [K0] at hgt; omega]
            ring_nf; linarith
          have hreQ : (resOrdExact c.d1 (2 * K0 - 1) c.d2 (2 * K0 - 2) : ℚ) +
              2 * ((c.d1 : ℚ) + (c.d2 : ℚ)) * ((k0 - K0 : ℕ) : ℚ) ≤
              (resOrdExact c.d1 (2 * k0 - 1) c.d2 (2 * k0 - 2) : ℚ) := by exact_mod_cast hre
          have hm := mul_le_mul_of_nonneg_left hreQ (show (0 : ℚ) ≤ (c.vres : ℚ) by positivity)
          linarith only [hm]
        · exact le_rfl
      have hstep_nn : (0 : ℚ) ≤ ((k0 - K0 : ℕ) : ℚ) := by positivity
      have hvx_nn : (0 : ℚ) ≤ (c.vx : ℚ) := by positivity
      have hvlc1_nn : (0 : ℚ) ≤ (c.vlc1 : ℚ) := by positivity
      have hvlc2_nn : (0 : ℚ) ≤ (c.vlc2 : ℚ) := by positivity
      have hrk_mul := mul_le_mul_of_nonneg_left htail_rk hvx_nn
      have hsl_mul := mul_le_mul_of_nonneg_right hslQ hstep_nn
      have hlc1_mul := mul_le_mul_of_nonneg_left hlc1_t hvlc1_nn
      have hlc2_mul := mul_le_mul_of_nonneg_left hlc2_t hvlc2_nn
      split_ifs at hbase hres_t hsl_mul ⊢ <;>
        linarith only [hα_max, hbase, hmax_mono, hrk_mul, hsl_mul, hlc1_mul, hlc2_mul, hres_t]
  -- Sum over i : Idx and divide by N!
  let L (x : ℚ) : ℚ :=
    (c.unNum : ℚ) / (mDen : ℚ) - (c.ua : ℚ) * ((A : ℚ) / (N : ℚ)) +
    (c.vf1 : ℚ) * (((x - 1) * (wY : ℚ) + 1) / (N : ℚ)) +
    (c.vf2 : ℚ) * (((x - 2) * (wY : ℚ) + 2) / (N : ℚ)) +
    (c.vlc1 : ℚ) * (((x - 1 - (c.d1 : ℚ)) * (wY : ℚ) + 1) / (N : ℚ)) +
    (c.vlc2 : ℚ) * (((x - 2 - (c.d2 : ℚ)) * (wY : ℚ) + 2) / (N : ℚ)) +
    (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then
      (c.vres : ℚ) * ((((c.d2 : ℚ) * (x - 1) + (c.d1 : ℚ) * (x - 2) - (c.d1 : ℚ) * (c.d2 : ℚ)) * (wY : ℚ) +
        ((c.d2 : ℚ) + 2 * (c.d1 : ℚ))) / (N : ℚ))
     else 0)
  have hsum_all : (c.vx : ℚ) * ((∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) / (N : ℚ)) ≤ L cVal := by
    have hpt_i : ∀ i : Idx,
        (c.vx : ℚ) * rankDiffQ 2 c.m c.s (k i) + (c.ua : ℚ) * (if i ∈ Az then (1 : ℚ) else 0) ≤
        (c.unNum : ℚ) / (mDen : ℚ) +
        (c.vf1 : ℚ) * ((if i ∈ Az then (1 : ℚ) else 0) * ((2 * k i - 1 : ℕ) : ℚ)) +
        (c.vf2 : ℚ) * ((if i ∈ Az then (1 : ℚ) else 0) * ((2 * k i - 2 : ℕ) : ℚ)) +
        (c.vlc1 : ℚ) * ((2 * k i - 1 - c.d1 : ℕ) : ℚ) + (c.vlc2 : ℚ) * ((2 * k i - 2 - c.d2 : ℕ) : ℚ) +
        (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then (c.vres : ℚ) * (resOrdExact c.d1 (2 * k i - 1) c.d2 (2 * k i - 2) : ℚ) else 0) :=
      fun i => hpt_all (k i) (if i ∈ Az then 1 else 0) (by split_ifs <;> simp)
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt_i i
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hcardIdx] at hsum
    have hAz_sum : (∑ i : Idx, if i ∈ Az then (1 : ℚ) else 0) = (Az.card : ℚ) := by simp [Finset.sum_ite_mem]
    have hf1_sum : (∑ i : Idx, (if i ∈ Az then (1 : ℚ) else 0) * ((2 * k i - 1 : ℕ) : ℚ)) =
        ∑ i ∈ Az, ((2 * k i - 1 : ℕ) : ℚ) := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    have hf2_sum : (∑ i : Idx, (if i ∈ Az then (1 : ℚ) else 0) * ((2 * k i - 2 : ℕ) : ℚ)) =
        ∑ i ∈ Az, ((2 * k i - 2 : ℕ) : ℚ) := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    rw [hAz_sum, hf1_sum, hf2_sum] at hsum
    have hAzQ : (A : ℚ) ≤ (Az.card : ℚ) := by exact_mod_cast hAz
    have hres_sum : (∑ i : Idx, if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then
          (c.vres : ℚ) * (resOrdExact c.d1 (2 * k i - 1) c.d2 (2 * k i - 2) : ℚ) else 0) ≤
        (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then
          (c.vres : ℚ) * (((c.d2 : ℚ) * (cVal - 1) + (c.d1 : ℚ) * (cVal - 2) - (c.d1 : ℚ) * (c.d2 : ℚ)) * (wY : ℚ) +
            ((c.d2 : ℚ) + 2 * (c.d1 : ℚ))) else 0) := by
      split_ifs with hr
      · rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hres hr) (by positivity)
      · simp
    have hcomb : (c.vx : ℚ) * (∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) ≤ (N : ℚ) * L cVal := by
      have hNL : (N : ℚ) * L cVal =
          (N : ℚ) * ((c.unNum : ℚ) / (mDen : ℚ)) - (c.ua : ℚ) * (A : ℚ) +
          (c.vf1 : ℚ) * ((cVal - 1) * (wY : ℚ) + 1) +
          (c.vf2 : ℚ) * ((cVal - 2) * (wY : ℚ) + 2) +
          (c.vlc1 : ℚ) * ((cVal - 1 - (c.d1 : ℚ)) * (wY : ℚ) + 1) +
          (c.vlc2 : ℚ) * ((cVal - 2 - (c.d2 : ℚ)) * (wY : ℚ) + 2) +
          (if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then
            (c.vres : ℚ) * (((c.d2 : ℚ) * (cVal - 1) + (c.d1 : ℚ) * (cVal - 2) - (c.d1 : ℚ) * (c.d2 : ℚ)) * (wY : ℚ) +
              ((c.d2 : ℚ) + 2 * (c.d1 : ℚ))) else 0) := by
        dsimp only [L]; split_ifs <;> (field_simp [hNQ.ne']; try ring)
      rw [hNL]
      have h1 := mul_le_mul_of_nonneg_left hAzQ (show (0 : ℚ) ≤ (c.ua : ℚ) by positivity)
      have h2 := mul_le_mul_of_nonneg_left hf1 (show (0 : ℚ) ≤ (c.vf1 : ℚ) by positivity)
      have h3 := mul_le_mul_of_nonneg_left hf2 (show (0 : ℚ) ≤ (c.vf2 : ℚ) by positivity)
      have h4 := mul_le_mul_of_nonneg_left hlc1 (show (0 : ℚ) ≤ (c.vlc1 : ℚ) by positivity)
      have h5 := mul_le_mul_of_nonneg_left hlc2 (show (0 : ℚ) ≤ (c.vlc2 : ℚ) by positivity)
      linarith
    rw [← mul_div_assoc, div_le_iff₀' hNQ]
    exact hcomb
  have hL_affine : ∀ (x y t : ℚ), L ((1 - t) * x + t * y) = (1 - t) * L x + t * L y := by
    intro x y t; dsimp only [L]; split_ifs <;> ring
  set t : ℚ := (cVal - (c.cLoNum : ℚ) / (c.cLoDen : ℚ)) /
      ((c.cHiNum : ℚ) / (c.cHiDen : ℚ) - (c.cLoNum : ℚ) / (c.cLoDen : ℚ))
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) (sub_pos.mpr hcltQ).le
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hcltQ)).mpr (sub_le_sub_right hhi _)
  have hcVal_eq : cVal = (1 - t) * ((c.cLoNum : ℚ) / (c.cLoDen : ℚ)) + t * ((c.cHiNum : ℚ) / (c.cHiDen : ℚ)) :=
    linear_interp_eq hcltQ
  have hL_ep : ∀ (cNum cDen : ℕ) (hcD : 0 < cDen), checkT2Endpoint c cNum cDen = true →
      (c.m = 0 → L ((cNum : ℚ) / (cDen : ℚ)) < 0) ∧
      (0 < c.m → L ((cNum : ℚ) / (cDen : ℚ)) - (c.vx : ℚ) * vquotLbQ 2 c.m c.s ((cNum : ℚ) / (cDen : ℚ)) <
        -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ))) := by
    intro cNum cDen hcD hep
    have hcDQ : (0 : ℚ) < (cDen : ℚ) := by exact_mod_cast hcD
    have hwYQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY, D]
    unfold checkT2Endpoint at hep; dsimp only at hep
    set linZ : ℤ :=
      -(c.ua : ℤ) * (A : ℤ) * (cDen : ℤ) +
      (c.vf1 : ℤ) * (((cNum : ℤ) - (cDen : ℤ)) * (wY : ℤ) + (cDen : ℤ)) +
      (c.vf2 : ℤ) * (((cNum : ℤ) - 2 * (cDen : ℤ)) * (wY : ℤ) + 2 * (cDen : ℤ)) +
      (c.vlc1 : ℤ) * (((cNum : ℤ) - (1 + (c.d1 : ℤ)) * (cDen : ℤ)) * (wY : ℤ) + (cDen : ℤ)) +
      (c.vlc2 : ℤ) * (((cNum : ℤ) - (2 + (c.d2 : ℤ)) * (cDen : ℤ)) * (wY : ℤ) + 2 * (cDen : ℤ)) +
      if 1 ≤ c.d1 ∧ 2 ≤ c.d2 then
        (c.vres : ℤ) * (((c.d2 : ℤ) * ((cNum : ℤ) - (cDen : ℤ)) + (c.d1 : ℤ) * ((cNum : ℤ) - 2 * (cDen : ℤ)) -
          (c.d1 : ℤ) * (c.d2 : ℤ) * (cDen : ℤ)) * (wY : ℤ) + ((c.d2 : ℤ) + 2 * (c.d1 : ℤ)) * (cDen : ℤ))
      else 0
    have hL_eq : L ((cNum : ℚ) / (cDen : ℚ)) =
        ((c.unNum : ℚ) * (N : ℚ) * (cDen : ℚ) + (linZ : ℚ) * (mDen : ℚ)) / ((N : ℚ) * (mDen : ℚ) * (cDen : ℚ)) := by
      dsimp only [L, linZ]
      split_ifs <;> (push_cast; field_simp [hNQ.ne', hmDenQ.ne', hcDQ.ne']; ring)
    constructor
    · intro hm0
      have hm0b : (c.m == 0) = true := beq_iff_eq.mpr hm0
      rw [if_pos hm0b] at hep
      have hZ : c.unNum * (N : ℤ) * (cDen : ℤ) + linZ < 0 := by
        simpa [linZ, decide_eq_true_eq] using decide_eq_true_eq.mp hep
      have hm1 : (mDen : ℚ) = 1 := by dsimp [mDen]; simp [hm0b]
      rw [hL_eq, hm1, mul_one, mul_one]
      exact div_neg_of_neg_of_pos (by exact_mod_cast hZ) (by positivity)
    · intro hmpos
      have hm0b : (c.m == 0) = false := beq_false_of_ne (Nat.ne_of_gt hmpos)
      rw [if_neg (by simp [hm0b])] at hep
      have hδD : 0 < c.δDen := by by_contra h; simp [Nat.ne_of_gt hmpos, show c.δDen = 0 by omega] at h4
      have hδDQ : (0 : ℚ) < (c.δDen : ℚ) := by exact_mod_cast hδD
      have hZ := decide_eq_true_eq.mp hep
      have hv := vquotNum_div_eq 2 c.m c.s hmpos cNum cDen (by exact_mod_cast hcD)
      simp only [Int.cast_natCast] at hv
      have hmDen_eq : (mDen : ℚ) = (c.m : ℚ) * (c.m : ℚ) := by dsimp [mDen]; simp [hm0b]
      have hvD_eq : (vquotDen c.m cDen : ℚ) = (N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (cDen : ℚ) := by
        unfold vquotDen; rw [hmDen_eq]; push_cast; ring
      have hsub_eq : L ((cNum : ℚ) / (cDen : ℚ)) - (c.vx : ℚ) * vquotLbQ 2 c.m c.s ((cNum : ℚ) / (cDen : ℚ)) =
          (((c.unNum : ℚ) * (N : ℚ) * (cDen : ℚ) + (linZ : ℚ) * (mDen : ℚ)) * (8 * (wY : ℚ) * (cDen : ℚ)) -
            (c.vx : ℚ) * (vquotNum 2 c.m c.s cNum cDen : ℚ)) /
          ((N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (cDen : ℚ)) := by
        rw [hL_eq, ← hv, hvD_eq]; field_simp [hNQ.ne', hmDenQ.ne', hcDQ.ne', hwYQ.ne']
      rw [hsub_eq]
      have hDpos : (0 : ℚ) < (N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (cDen : ℚ) := by positivity
      rw [show -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) = -((c.vx : ℚ) * (c.δNum : ℚ)) / (c.δDen : ℚ) by ring]
      rw [div_lt_div_iff₀ hDpos hδDQ]
      have hQ : (((c.unNum : ℤ) * (N : ℤ) * (cDen : ℤ) + linZ * mDen) * (8 * (wY : ℤ) * (cDen : ℤ)) -
          (c.vx : ℤ) * vquotNum 2 c.m c.s cNum cDen : ℚ) * (c.δDen : ℚ) <
          -((c.vx : ℚ) * (c.δNum : ℚ) * ((N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (cDen : ℚ))) := by
        have hZ' : ((c.unNum * (N : ℤ) * (cDen : ℤ) + linZ * mDen) * (8 * (wY : ℤ) * (cDen : ℤ)) -
            (c.vx : ℤ) * vquotNum 2 c.m c.s cNum cDen) * (c.δDen : ℤ) <
            -((c.vx : ℤ) * (c.δNum : ℤ) * ((N : ℤ) * mDen * (8 * (wY : ℤ) * (cDen : ℤ)) * (cDen : ℤ))) := by
          simpa [linZ, mDen, hm0b, decide_eq_true_eq] using hZ
        exact_mod_cast hZ'
      push_cast at hQ; linarith
  have hLo := hL_ep c.cLoNum c.cLoDen hcLoD hepLo
  have hHi := hL_ep c.cHiNum c.cHiDen hcHiD hepHi
  constructor
  · intro hm0
    have hvx0 : c.vx = 0 := by by_contra hne; simp [hm0, hne] at h3
    have hL_lt : L cVal < 0 := by rw [hcVal_eq, hL_affine]; exact convex_comb_lt ht0 ht1 (hLo.1 hm0) (hHi.1 hm0)
    have h0le : (0 : ℚ) ≤ L cVal := by simpa [hvx0] using hsum_all
    linarith
  · intro hmpos
    have hm0b : (c.m == 0) = false := beq_false_of_ne (Nat.ne_of_gt hmpos)
    have hvxpos : 0 < c.vx := by by_contra h; simp [Nat.ne_of_gt hmpos, show c.vx = 0 by omega] at h4
    have hvxQ : (0 : ℚ) < (c.vx : ℚ) := by exact_mod_cast hvxpos
    have hsec := vquotLbQ_ge_secant 2 c.m c.s hmpos hlo hhi hcltQ
    have hL_lt : L cVal - (c.vx : ℚ) * vquotLbQ 2 c.m c.s cVal < -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) := by
      have hlin : (1 - t) * (L ((c.cLoNum : ℚ) / (c.cLoDen : ℚ)) - (c.vx : ℚ) * vquotLbQ 2 c.m c.s ((c.cLoNum : ℚ) / (c.cLoDen : ℚ))) +
          t * (L ((c.cHiNum : ℚ) / (c.cHiDen : ℚ)) - (c.vx : ℚ) * vquotLbQ 2 c.m c.s ((c.cHiNum : ℚ) / (c.cHiDen : ℚ))) <
          -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) :=
        convex_comb_lt ht0 ht1 (hLo.2 hmpos) (hHi.2 hmpos)
      have hL_c : L cVal = (1 - t) * L ((c.cLoNum : ℚ) / (c.cLoDen : ℚ)) + t * L ((c.cHiNum : ℚ) / (c.cHiDen : ℚ)) := by
        rw [← hL_affine, ← hcVal_eq]
      have hsec_m := mul_le_mul_of_nonneg_left hsec hvxQ.le
      linarith only [hlin, hL_c, hsec_m]
    rw [if_neg (by simp [hm0b])] at hcap
    refine ⟨?_, hcap⟩
    have h1 : (c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) <
        (c.vx : ℚ) * (vquotLbQ 2 c.m c.s cVal - (∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) / (N : ℚ)) := by
      linarith only [hL_lt, hsum_all]
    exact lt_of_mul_lt_mul_left h1 hvxQ.le

/-! ### Part 4: Table 3 (`deg_R = 2`, `gcd(f_1, f_2) = g` non-constant) pure-`Int` checker & soundness -/

/-- Mode tag for Table 3 certificates:
- `0` = `"std"`, `1` = `"vpln"`, `2` = `"h11"`, `3` = `"2A"`. -/
def t3Vrf0Ord (mode dg dStarEff k rr : ℕ) : ℕ :=
  if k == 0 then 0
  else if mode == 3 then
    let halfDs := dStarEff / 2
    let halfDg := dg / 2
    let evalRq (rq : ℕ) : ℕ :=
      let rre := rr - rq
      let vk := (2 * resOrdWeighted2Fast halfDs (2 * k + 2) halfDg rre - 2 * dg) + dStarEff * rq
      let vp0 := resOrdExact 0 (2 * k - 2) dg rre + dStarEff * (rre - dg)
      let vp := ((List.range (dStarEff + 1)).map (fun d0 =>
        resOrdExact d0 (2 * k - 2) dg rre + (dStarEff - d0) * (rre - dg))).foldl Nat.min vp0 + dStarEff * rq
      max vk vp
    ((List.range (rr + 1)).filter (fun rq => (rr - rq) % 2 == 0)).foldl
      (fun acc rq => Nat.min acc (evalRq rq)) (evalRq rr)
  else if mode == 1 || mode == 2 then
    let vk := resOrdWeighted2Fast dStarEff (4 * k + 4) (dg / 2) rr - 2 * dg
    let vp0 := resOrdExact 0 (2 * k - 2) dg rr + dStarEff * (rr - dg)
    let vp := ((List.range (dStarEff + 1)).map (fun d0 =>
      resOrdExact d0 (2 * k - 2) dg rr + (dStarEff - d0) * (rr - dg))).foldl Nat.min vp0
    max vk vp
  else
    resOrdWeighted2Fast dStarEff (4 * k + 4) (dg / 2) rr - 2 * dg

/-- Exact closed form of `t3Vrf0Ord` whenever `k ≥ dStarEff + 3` and `dg` is even (and `dStarEff` even for mode 3):
`t3Vrf0Ord mode dg dStarEff k rr = 2 * dg * k + dStarEff * rr - dStarEff * dg`! -/
lemma t3Vrf0Ord_eq_large (mode dg dStarEff k rr : ℕ)
    (hdg_pos : 0 < dg) (hds_pos : 0 < dStarEff)
    (hdg_even : 2 * (dg / 2) = dg) (hds_even : mode = 3 → 2 * (dStarEff / 2) = dStarEff)
    (hk : dStarEff + 3 ≤ k) :
    t3Vrf0Ord mode dg dStarEff k rr = 2 * dg * k + dStarEff * rr - dStarEff * dg := by
  have hk0 : (k == 0) = false := by simp; omega
  have hdg_half_pos : 0 < dg / 2 := by omega
  have h2km2 : dStarEff + 4 ≤ 2 * k - 2 := by omega
  have hvp_le : ∀ (rre : ℕ),
      ((List.range (dStarEff + 1)).map (fun d0 =>
        resOrdExact d0 (2 * k - 2) dg rre + (dStarEff - d0) * (rre - dg))).foldl Nat.min
          (resOrdExact 0 (2 * k - 2) dg rre + dStarEff * (rre - dg)) ≤
      2 * dg * k + dStarEff * rre - dStarEff * dg := by
    intro rre
    have hfold_le_mem : ∀ (l : List ℕ) (init x : ℕ), x ∈ l → l.foldl Nat.min init ≤ x := by
      intro l
      induction l with
      | nil => intro _ _ hx; cases hx
      | cons a t ih =>
        intro init x hx
        simp only [List.foldl_cons, List.mem_cons] at hx ⊢
        rcases hx with rfl | ht
        · have hle : ∀ (l' : List ℕ) (z : ℕ), l'.foldl Nat.min z ≤ z := by
            intro l'; induction l' with
            | nil => intro _; exact le_rfl
            | cons b bs ih' => intro z; simp only [List.foldl_cons]; exact (ih' _).trans (Nat.min_le_left _ _)
          exact (hle t _).trans (Nat.min_le_right _ _)
        · exact ih _ x ht
    have hmem : resOrdExact dStarEff (2 * k - 2) dg rre + (dStarEff - dStarEff) * (rre - dg) ∈
        (List.range (dStarEff + 1)).map (fun d0 =>
          resOrdExact d0 (2 * k - 2) dg rre + (dStarEff - d0) * (rre - dg)) :=
      List.mem_map.mpr ⟨dStarEff, List.mem_range.mpr (Nat.lt_succ_self _), rfl⟩
    refine (hfold_le_mem _ _ _ hmem).trans ?_
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    unfold resOrdExact
    have hds0 : dStarEff ≠ 0 := Nat.ne_of_gt hds_pos
    have hdg0 : dg ≠ 0 := Nat.ne_of_gt hdg_pos
    simp only [hds0, hdg0, ↓reduceIte]
    have h0 : dStarEff - (2 * k - 2) = 0 := by omega
    rw [h0, Nat.zero_mul, Nat.add_zero]
    have h1 : dStarEff * dg ≤ dg * (2 * k - 2) + dStarEff * rre := by nlinarith
    have h2 : dStarEff * dg ≤ 2 * dg * k + dStarEff * rre := by nlinarith
    zify [h1, h2, show 2 ≤ 2 * k by omega]; nlinarith
  have hvk_std : resOrdWeighted dStarEff (4 * k + 4) (dg / 2) rr 2 - 2 * dg =
      2 * dg * k + dStarEff * rr - dStarEff * dg := by
    rw [resOrdWeighted_eq_of_two_mul_le dStarEff (4 * k + 4) (dg / 2) rr hds_pos hdg_half_pos (by omega)]
    have h1 : 2 * dStarEff * (dg / 2) ≤ (dg / 2) * (4 * k + 4) + dStarEff * rr := by nlinarith
    have h2 : 2 * dg ≤ (dg / 2) * (4 * k + 4) + dStarEff * rr - 2 * dStarEff * (dg / 2) := by
      zify [h1]; nlinarith
    have h3 : dStarEff * dg ≤ 2 * dg * k + dStarEff * rr := by nlinarith
    zify [h1, h2, h3]; nlinarith
  unfold t3Vrf0Ord
  simp only [hk0, Bool.false_eq_true, ↓reduceIte, resOrdWeighted2Fast_eq]
  by_cases hm3 : mode = 3
  · subst hm3
    simp only [beq_self_eq_true, ↓reduceIte]
    have hds2 : 2 * (dStarEff / 2) = dStarEff := hds_even rfl
    have hds_half_pos : 0 < dStarEff / 2 := by omega
    have hvk_eq : ∀ rq ≤ rr,
        (2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) (rr - rq) 2 - 2 * dg) + dStarEff * rq =
        2 * dg * k + dStarEff * rr - dStarEff * dg := by
      intro rq hrq
      rw [resOrdWeighted_eq_of_two_mul_le (dStarEff / 2) (2 * k + 2) (dg / 2) (rr - rq)
        hds_half_pos hdg_half_pos (by omega)]
      have h1 : 2 * (dStarEff / 2) * (dg / 2) ≤ (dg / 2) * (2 * k + 2) + (dStarEff / 2) * (rr - rq) := by nlinarith
      have h2 : 2 * dg ≤ 2 * ((dg / 2) * (2 * k + 2) + (dStarEff / 2) * (rr - rq) - 2 * (dStarEff / 2) * (dg / 2)) := by
        zify [h1]; nlinarith
      have h3 : dStarEff * dg ≤ 2 * dg * k + dStarEff * rr := by nlinarith
      zify [h1, h2, h3, hrq]; nlinarith
    have heval_eq : ∀ rq ≤ rr,
        max ((2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) (rr - rq) 2 - 2 * dg) + dStarEff * rq)
          (((List.range (dStarEff + 1)).map (fun d0 =>
            resOrdExact d0 (2 * k - 2) dg (rr - rq) + (dStarEff - d0) * (rr - rq - dg))).foldl Nat.min
              (resOrdExact 0 (2 * k - 2) dg (rr - rq) + dStarEff * (rr - rq - dg)) + dStarEff * rq) =
        2 * dg * k + dStarEff * rr - dStarEff * dg := by
      intro rq hrq
      rw [hvk_eq rq hrq]
      apply Nat.max_eq_left
      have hvp := hvp_le (rr - rq)
      have h3 : dStarEff * dg ≤ 2 * dg * k + dStarEff * (rr - rq) := by nlinarith
      have h4 : dStarEff * dg ≤ 2 * dg * k + dStarEff * rr := by nlinarith
      zify [h3, h4, hrq] at hvp ⊢; nlinarith
    have hfold_const : ∀ (l : List ℕ) (f : ℕ → ℕ) (C : ℕ),
        (∀ x ∈ l, f x = C) → l.foldl (fun acc x => Nat.min acc (f x)) C = C := by
      intro l f C hC
      induction l with
      | nil => rfl
      | cons a t ih =>
        simp only [List.foldl_cons, hC a (by simp), Nat.min_self]
        exact ih (fun x hx => hC x (by simp [hx]))
    show ((List.range (rr + 1)).filter (fun rq => (rr - rq) % 2 == 0)).foldl
      (fun acc rq => Nat.min acc (max ((2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) (rr - rq) 2 - 2 * dg) + dStarEff * rq)
          (((List.range (dStarEff + 1)).map (fun d0 =>
            resOrdExact d0 (2 * k - 2) dg (rr - rq) + (dStarEff - d0) * (rr - rq - dg))).foldl Nat.min
              (resOrdExact 0 (2 * k - 2) dg (rr - rq) + dStarEff * (rr - rq - dg)) + dStarEff * rq)))
      (max ((2 * resOrdWeighted (dStarEff / 2) (2 * k + 2) (dg / 2) (rr - rr) 2 - 2 * dg) + dStarEff * rr)
          (((List.range (dStarEff + 1)).map (fun d0 =>
            resOrdExact d0 (2 * k - 2) dg (rr - rr) + (dStarEff - d0) * (rr - rr - dg))).foldl Nat.min
              (resOrdExact 0 (2 * k - 2) dg (rr - rr) + dStarEff * (rr - rr - dg)) + dStarEff * rr)) = _
    rw [heval_eq rr le_rfl]
    apply hfold_const
    intro rq hrq
    exact heval_eq rq (Nat.lt_succ_iff.mp (List.mem_range.mp (List.mem_filter.mp hrq).1))
  · have hm3b : (mode == 3) = false := beq_false_of_ne hm3
    simp only [hm3b, Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · rw [hvk_std]; exact Nat.max_eq_left (hvp_le rr)
    · exact hvk_std

/-- Table 3 certificate (`mode ∈ {0: std, 1: vpln, 2: h11, 3: 2A}`). -/
structure T3Cert where
  d2 : ℕ
  dg : ℕ
  d1 : ℕ
  hasDStar : Bool
  dStar : ℕ
  mode : ℕ
  cLoNum : ℕ
  cLoDen : ℕ
  cHiNum : ℕ
  cHiDen : ℕ
  m : ℕ
  s : ℕ
  ua : ℕ
  vg : ℕ
  vh1 : ℕ
  vh2 : ℕ
  vlcg : ℕ
  vlch1 : ℕ
  vlch2 : ℕ
  vrh : ℕ
  vrf0 : ℕ
  vx : ℕ
  vh11 : ℕ
  unNum : ℤ
  δNum : ℕ
  δDen : ℕ
  cap : CapWitness
  deriving Repr

/-- Check one corner `(c, cg) = (cNum / cDen, cgNum / cgDen)` of a Table 3 certificate in pure `Int`! -/
def checkT3Corner (c : T3Cert) (cNum cDen cgNum cgDen : ℕ) : Bool :=
  let dh2 : ℤ := (c.d2 - c.dg : ℕ)
  let dh1 : ℤ := (c.d1 - c.dg : ℕ)
  let hasRh : Bool := decide (1 ≤ c.d1 - c.dg ∧ 2 ≤ c.d2 - c.dg)
  let hasH11 : Bool := (c.mode == 2)
  let dStarEff : ℤ := if c.mode == 3 then ((c.dStar - 1 : ℕ) : ℤ) else (c.dStar : ℤ)
  let mDen : ℤ := if c.m == 0 then 1 else (c.m : ℤ) * (c.m : ℤ)
  -- Express everything over common denominator `D_lin = N * cDen * cgDen`:
  let cZ : ℤ := (cNum : ℤ) * (cgDen : ℤ)
  let cgZ : ℤ := (cgNum : ℤ) * (cDen : ℤ)
  let uZ : ℤ := (cDen : ℤ) * (cgDen : ℤ)
  let linNum : ℤ :=
    -(c.ua : ℤ) * (A : ℤ) * uZ +
    (c.vg : ℤ) * (cgZ * (wY : ℤ)) +
    (c.vh1 : ℤ) * ((cZ - uZ - cgZ) * (wY : ℤ) + uZ) +
    (c.vh2 : ℤ) * ((cZ - 2 * uZ - cgZ) * (wY : ℤ) + 2 * uZ) +
    (c.vlcg : ℤ) * ((cgZ - (c.dg : ℤ) * uZ) * (wY : ℤ)) +
    (c.vlch1 : ℤ) * ((cZ - (1 + dh1) * uZ - cgZ) * (wY : ℤ) + uZ) +
    (c.vlch2 : ℤ) * ((cZ - (2 + dh2) * uZ - cgZ) * (wY : ℤ) + 2 * uZ) +
    (if hasRh then
      (c.vrh : ℤ) * ((dh2 * (cZ - uZ - cgZ) + dh1 * (cZ - 2 * uZ - cgZ) - dh1 * dh2 * uZ) * (wY : ℤ) +
        (dh2 + 2 * dh1) * uZ) else 0) +
    (if c.hasDStar then
      (c.vrf0 : ℤ) * (((c.dg : ℤ) * (cZ - dStarEff * uZ) + dStarEff * cgZ) * (wY : ℤ)) else 0) +
    (if hasH11 then
      (c.vh11 : ℤ) * ((cZ - 4 * uZ - cgZ) * (wY : ℤ) + uZ) else 0)
  if c.m == 0 then
    c.unNum * (N : ℤ) * uZ + linNum < 0
  else
    let vN : ℤ := vquotNum 2 c.m c.s (cNum : ℤ) (cDen : ℤ)
    -- vquotLbQ = vN / (N * mDen * 8 * wY * cDen^2)
    -- Put both over D = N * mDen * 8 * wY * cDen^2 * cgDen:
    let scale : ℤ := 8 * (wY : ℤ) * (cDen : ℤ)
    let objNum : ℤ := (c.unNum * (N : ℤ) * uZ + linNum * mDen) * scale - (c.vx : ℤ) * vN * (cgDen : ℤ)
    let D : ℤ := (N : ℤ) * mDen * scale * uZ
    objNum * (c.δDen : ℤ) < -((c.vx : ℤ) * (c.δNum : ℤ) * D)

/-- Tail-recursive pure-`ℕ` universal boolean quantifier over `0 .. n-1` (zero `List` allocation). -/
def allNat : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p n && allNat n p

private lemma allNat_eq_true_iff (n : ℕ) (p : ℕ → Bool) :
    allNat n p = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [allNat]
  | succ n ih =>
    simp only [allNat, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hn, hlt⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact hlt i h
      · exact hn
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

/-- Pure-`ℕ` version of `rankDiffNum` using `rankKerDFast`. -/
def rkDiffNat (d m s k : ℕ) : ℕ :=
  if m == 0 then 0 else rankKerDFast m s - rankKerDFast (m - k) (s - d)

private lemma rkDiffNat_cast (d m s k : ℕ) :
    (rkDiffNat d m s k : ℤ) = rankDiffNum d m s k := by
  unfold rkDiffNat rankDiffNum
  by_cases hm : m = 0
  · simp [hm]
  · have hmb : (m == 0) = false := beq_false_of_ne hm
    simp only [hmb, Bool.false_eq_true, ↓reduceIte]
    have hle : rankKerDFast (m - k) (s - d) ≤ rankKerDFast m s := by
      rw [rankKerDFast_eq, rankKerDFast_eq]
      exact (rankKerD_mono_m (Nat.sub_le m k)).trans (rankKerD_mono_s (Nat.sub_le s d))
    exact Nat.cast_sub hle

private lemma nat_sub_cast_eq_max_zero (a b : ℕ) :
    ((a - b : ℕ) : ℤ) = max (0 : ℤ) ((a : ℤ) - (b : ℤ)) := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h, max_eq_right (by omega)]
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero, max_eq_left (by omega)]

private lemma h1U_ge_h1 (ua vg vh1 vh2 k rr : ℕ) (hrr : rr ≤ 2 * k) :
    ua - (vg * rr + vh1 * (2 * k - 1 - rr) + vh2 * (2 * k - 2 - rr)) ≤
      ua - max (min vg vh1 * (2 * k - 1)) (min vg (vh1 + vh2) * (2 * k - 2)) := by
  have h1 : min vg vh1 * (2 * k - 1) ≤ vg * rr + vh1 * (2 * k - 1 - rr) := by
    by_cases hr : rr ≤ 2 * k - 1
    · have hsum : rr + (2 * k - 1 - rr) = 2 * k - 1 := by omega
      have ha : min vg vh1 * rr ≤ vg * rr := Nat.mul_le_mul_right rr (Nat.min_le_left _ _)
      have hb : min vg vh1 * (2 * k - 1 - rr) ≤ vh1 * (2 * k - 1 - rr) :=
        Nat.mul_le_mul_right _ (Nat.min_le_right _ _)
      conv_lhs => rw [← hsum, mul_add]
      exact Nat.add_le_add ha hb
    · have hle : 2 * k - 1 ≤ rr := by omega
      calc min vg vh1 * (2 * k - 1) ≤ vg * (2 * k - 1) := Nat.mul_le_mul_right _ (Nat.min_le_left _ _)
        _ ≤ vg * rr := Nat.mul_le_mul_left vg hle
        _ ≤ vg * rr + vh1 * (2 * k - 1 - rr) := Nat.le_add_right _ _
  have h2 : min vg (vh1 + vh2) * (2 * k - 2) ≤ vg * rr + vh1 * (2 * k - 1 - rr) + vh2 * (2 * k - 2 - rr) := by
    have hmid : vg * rr + (vh1 + vh2) * (2 * k - 2 - rr) ≤
        vg * rr + vh1 * (2 * k - 1 - rr) + vh2 * (2 * k - 2 - rr) := by
      have hsub : 2 * k - 2 - rr ≤ 2 * k - 1 - rr := by omega
      have hm := Nat.mul_le_mul_left vh1 hsub
      rw [add_mul]; omega
    refine le_trans ?_ hmid
    by_cases hr : rr ≤ 2 * k - 2
    · have hsum : rr + (2 * k - 2 - rr) = 2 * k - 2 := by omega
      have ha : min vg (vh1 + vh2) * rr ≤ vg * rr := Nat.mul_le_mul_right rr (Nat.min_le_left _ _)
      have hb : min vg (vh1 + vh2) * (2 * k - 2 - rr) ≤ (vh1 + vh2) * (2 * k - 2 - rr) :=
        Nat.mul_le_mul_right _ (Nat.min_le_right _ _)
      conv_lhs => rw [← hsum, mul_add]
      exact Nat.add_le_add ha hb
    · have hle : 2 * k - 2 ≤ rr := by omega
      calc min vg (vh1 + vh2) * (2 * k - 2) ≤ vg * (2 * k - 2) := Nat.mul_le_mul_right _ (Nat.min_le_left _ _)
        _ ≤ vg * rr := Nat.mul_le_mul_left vg hle
        _ ≤ vg * rr + (vh1 + vh2) * (2 * k - 2 - rr) := Nat.le_add_right _ _
  have hmax : max (min vg vh1 * (2 * k - 1)) (min vg (vh1 + vh2) * (2 * k - 2)) ≤
      vg * rr + vh1 * (2 * k - 1 - rr) + vh2 * (2 * k - 2 - rr) :=
    max_le (h1.trans (Nat.le_add_right _ _)) h2
  exact Nat.sub_le_sub_left hmax ua

def checkT3Cert (c : T3Cert) : Bool :=
  if c.cLoDen == 0 || c.cHiDen == 0 || c.dg == 0 || c.dg > c.d1 || c.dg > c.d2 then false
  else if !decide ((c.cLoNum : ℤ) * (c.cHiDen : ℤ) < (c.cHiNum : ℤ) * (c.cLoDen : ℤ)) then false
  else if c.dg % 2 != 0 then false
  else if c.hasDStar && (if c.mode == 3 then c.dStar ≤ 1 else c.dStar == 0) then false
  else if c.mode == 3 && (!c.hasDStar || c.dStar == 0 || (c.dStar - 1) % 2 != 0) then false
  else if c.m == 0 && c.vx != 0 then false
  else if c.m != 0 && (c.s < 2 || c.vx == 0 || c.δNum == 0 || c.δDen == 0) then false
  else if decide (c.unNum < 0) then false
  else
    let dh2 : ℕ := c.d2 - c.dg
    let dh1 : ℕ := c.d1 - c.dg
    let hasRh : Bool := decide (1 ≤ dh1 ∧ 2 ≤ dh2)
    let hasH11 : Bool := (c.mode == 2)
    let dStarEff : ℕ := if c.mode == 3 then c.dStar - 1 else c.dStar
    let K0 : ℕ := max (if c.hasDStar then c.dStar else 0) (max c.d1 c.d2) + 3
    let mDenNat : ℕ := if c.m == 0 then 1 else c.m * c.m
    let mDen : ℤ := (mDenNat : ℤ)
    let unNat : ℕ := c.unNum.toNat
    let slopeNum : ℤ := rankDiffNum 2 c.m c.s K0 - rankDiffNum 2 c.m c.s (K0 - 1)
    let slopeAOk : Bool :=
      (c.vx : ℤ) * slopeNum ≤
        (2 * (c.vlch1 : ℤ) + 2 * (c.vlch2 : ℤ) +
          (if hasRh then 2 * ((dh1 : ℤ) + (dh2 : ℤ)) * (c.vrh : ℤ) else 0) +
          (if c.hasDStar then 2 * (c.dg : ℤ) * (c.vrf0 : ℤ) else 0) +
          (if hasH11 then 2 * (c.vh11 : ℤ) else 0)) * mDen
    let slopeBOk : Bool :=
      (c.vx : ℤ) * slopeNum ≤
        (2 * (c.vlcg : ℤ) +
          (if c.hasDStar then 2 * ((c.dg : ℤ) + (dStarEff : ℤ)) * (c.vrf0 : ℤ) else 0)) * mDen
    let doRh : Bool := hasRh && (c.vrh != 0)
    let doRf0 : Bool := c.hasDStar && (c.vrf0 != 0)
    let doH11 : Bool := hasH11 && (c.vh11 != 0)
    let ptOk : Bool :=
      allNat (K0 + 1) fun k =>
        let rkN : ℕ := rkDiffNat 2 c.m c.s k
        let h1U : ℕ := c.ua - max (min c.vg c.vh1 * (2 * k - 1)) (min c.vg (c.vh1 + c.vh2) * (2 * k - 2))
        if Nat.ble (c.vx * rkN + h1U * mDenNat) unNat then true
        else
          allNat (2 * k + 1) fun rr =>
            let h1 : ℕ := c.ua - (c.vg * rr + c.vh1 * (2 * k - 1 - rr) + c.vh2 * (2 * k - 2 - rr))
            let baseSub : ℕ :=
              c.vlcg * (rr - c.dg) +
              c.vlch1 * (2 * k - 1 - rr - dh1) +
              c.vlch2 * (2 * k - 2 - rr - dh2) +
              (if doRh then c.vrh * resOrdExact dh1 (2 * k - 1 - rr) dh2 (2 * k - 2 - rr) else 0) +
              (if doH11 then c.vh11 * (2 * k - 2 - rr) else 0)
            if Nat.ble (c.vx * rkN + h1 * mDenNat) (unNat + baseSub * mDenNat) then true
            else if doRf0 then
              let rf0 : ℕ :=
                if Nat.ble (dStarEff + 3) k then 2 * c.dg * k + dStarEff * rr - dStarEff * c.dg
                else t3Vrf0Ord c.mode c.dg dStarEff k rr
              Nat.ble (c.vx * rkN + h1 * mDenNat) (unNat + (baseSub + c.vrf0 * rf0) * mDenNat)
            else false
    -- Exact 4 corners of `(c, cg)`: at `cLo` and `cHi`, `cg_min = dg` and `cg_max = max(dg, c - capCg + 2/wY)`!
    let capCg : ℕ := max (2 + dh2) (1 + dh1)
    let cgHiPair (cNum cDen : ℕ) : ℕ × ℕ :=
      -- c - capCg + 2/wY = (cNum * wY + 2 * cDen - capCg * cDen * wY) / (cDen * wY)
      let den := cDen * wY
      let lhs := cNum * wY + 2 * cDen
      let rhs := (c.dg + capCg) * den
      if lhs ≤ rhs then (c.dg, 1)
      else (lhs - capCg * den, den)
    let (cgLoHiN, cgLoHiD) := cgHiPair c.cLoNum c.cLoDen
    let (cgHiHiN, cgHiHiD) := cgHiPair c.cHiNum c.cHiDen
    let epOk : Bool :=
      checkT3Corner c c.cLoNum c.cLoDen c.dg 1 &&
      checkT3Corner c c.cLoNum c.cLoDen cgLoHiN cgLoHiD &&
      checkT3Corner c c.cHiNum c.cHiDen c.dg 1 &&
      checkT3Corner c c.cHiNum c.cHiDen cgHiHiN cgHiHiD
    let capOk : Bool :=
      if c.m == 0 then true
      else checkCapWitness 2 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 1 c.cap
    slopeAOk && slopeBOk && ptOk && epOk && capOk

/-- Soundness of `checkT3Cert` for ALL unbounded `(k i, rr i)` with `rr i ≤ 2 * k i`! -/
theorem checkT3Cert_sound (c : T3Cert) (hchk : checkT3Cert c = true)
    (cVal cgVal : ℚ)
    (hlo : (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ cVal)
    (hhi : cVal ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ))
    (hcg_lo : (c.dg : ℚ) ≤ cgVal)
    (hcg_hi : cgVal ≤ max (c.dg : ℚ) (cVal - ((max (2 + (c.d2 - c.dg)) (1 + (c.d1 - c.dg)) : ℕ) : ℚ) + 2 / (wY : ℚ)))
    (Az : Finset Idx) (hAz : A ≤ Az.card)
    (k rr : Idx → ℕ) (hrr_le : ∀ i, rr i ≤ 2 * k i)
    (hg : (∑ i ∈ Az, (rr i : ℚ)) ≤ cgVal * (wY : ℚ))
    (hh1 : (∑ i ∈ Az, ((2 * k i - 1 - rr i : ℕ) : ℚ)) ≤ (cVal - 1 - cgVal) * (wY : ℚ) + 1)
    (hh2 : (∑ i ∈ Az, ((2 * k i - 2 - rr i : ℕ) : ℚ)) ≤ (cVal - 2 - cgVal) * (wY : ℚ) + 2)
    (hlcg : (∑ i : Idx, ((rr i - c.dg : ℕ) : ℚ)) ≤ (cgVal - (c.dg : ℚ)) * (wY : ℚ))
    (hlch1 : (∑ i : Idx, ((2 * k i - 1 - rr i - (c.d1 - c.dg) : ℕ) : ℚ)) ≤
      (cVal - 1 - cgVal - ((c.d1 - c.dg : ℕ) : ℚ)) * (wY : ℚ) + 1)
    (hlch2 : (∑ i : Idx, ((2 * k i - 2 - rr i - (c.d2 - c.dg) : ℕ) : ℚ)) ≤
      (cVal - 2 - cgVal - ((c.d2 - c.dg : ℕ) : ℚ)) * (wY : ℚ) + 2)
    (hrh : 1 ≤ c.d1 - c.dg ∧ 2 ≤ c.d2 - c.dg →
      (∑ i : Idx, (resOrdExact (c.d1 - c.dg) (2 * k i - 1 - rr i) (c.d2 - c.dg) (2 * k i - 2 - rr i) : ℚ)) ≤
        (((c.d2 - c.dg : ℕ) : ℚ) * (cVal - 1 - cgVal) + ((c.d1 - c.dg : ℕ) : ℚ) * (cVal - 2 - cgVal) -
          ((c.d1 - c.dg : ℕ) : ℚ) * ((c.d2 - c.dg : ℕ) : ℚ)) * (wY : ℚ) +
          (((c.d2 - c.dg : ℕ) : ℚ) + 2 * ((c.d1 - c.dg : ℕ) : ℚ)))
    (hrf0 : c.hasDStar = true →
      let dStarEff : ℕ := if c.mode == 3 then c.dStar - 1 else c.dStar
      (∑ i : Idx, (t3Vrf0Ord c.mode c.dg dStarEff (k i) (rr i) : ℚ)) ≤
        ((c.dg : ℚ) * (cVal - (dStarEff : ℚ)) + (dStarEff : ℚ) * cgVal) * (wY : ℚ))
    (hh11 : c.mode = 2 →
      (∑ i : Idx, ((2 * k i - 2 - rr i : ℕ) : ℚ)) ≤ (cVal - 4 - cgVal) * (wY : ℚ) + 1) :
    (c.m = 0 → False) ∧
    (0 < c.m →
      (c.δNum : ℚ) / (c.δDen : ℚ) <
        vquotLbQ 2 c.m c.s cVal - (∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) / (N : ℚ) ∧
      checkCapWitness 2 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 1 c.cap = true) := by
  unfold checkT3Cert at hchk
  dsimp only at hchk
  by_cases h1 : (c.cLoDen == 0 || c.cHiDen == 0 || c.dg == 0 || c.dg > c.d1 || c.dg > c.d2) = true
  · rw [if_pos h1] at hchk; cases hchk
  rw [if_neg h1] at hchk
  by_cases h2 : (!decide ((c.cLoNum : ℤ) * (c.cHiDen : ℤ) < (c.cHiNum : ℤ) * (c.cLoDen : ℤ))) = true
  · rw [if_pos h2] at hchk; cases hchk
  rw [if_neg h2] at hchk
  by_cases h3 : (c.dg % 2 != 0) = true
  · rw [if_pos h3] at hchk; cases hchk
  rw [if_neg h3] at hchk
  by_cases h3b : (c.hasDStar && (if c.mode == 3 then c.dStar ≤ 1 else c.dStar == 0)) = true
  · rw [if_pos h3b] at hchk; cases hchk
  rw [if_neg h3b] at hchk
  by_cases h4 : (c.mode == 3 && (!c.hasDStar || c.dStar == 0 || (c.dStar - 1) % 2 != 0)) = true
  · rw [if_pos h4] at hchk; cases hchk
  rw [if_neg h4] at hchk
  by_cases h5 : (c.m == 0 && c.vx != 0) = true
  · rw [if_pos h5] at hchk; cases hchk
  rw [if_neg h5] at hchk
  by_cases h6 : (c.m != 0 && (c.s < 2 || c.vx == 0 || c.δNum == 0 || c.δDen == 0)) = true
  · rw [if_pos h6] at hchk; cases hchk
  rw [if_neg h6] at hchk
  by_cases h7 : decide (c.unNum < 0) = true
  · rw [if_pos h7] at hchk; cases hchk
  rw [if_neg h7] at hchk
  have hun_nn : 0 ≤ c.unNum := by
    by_contra hlt; push Not at hlt; exact h7 (decide_eq_true hlt)
  have hun_toNat : (c.unNum.toNat : ℤ) = c.unNum := Int.toNat_of_nonneg hun_nn
  have hcLoD : 0 < c.cLoDen := by by_contra h; simp [show c.cLoDen = 0 by omega] at h1
  have hcHiD : 0 < c.cHiDen := by by_contra h; simp [show c.cHiDen = 0 by omega] at h1
  have hdg_pos : 0 < c.dg := by by_contra h; simp [show c.dg = 0 by omega] at h1
  have hdg1 : c.dg ≤ c.d1 := by by_contra h; simp [show c.dg > c.d1 by omega] at h1
  have hdg2 : c.dg ≤ c.d2 := by by_contra h; simp [show c.dg > c.d2 by omega] at h1
  have hdg_even : 2 * (c.dg / 2) = c.dg := by
    have : c.dg % 2 = 0 := by by_contra hne; simp [hne] at h3
    omega
  have hds_pos : c.hasDStar = true → 0 < (if c.mode == 3 then c.dStar - 1 else c.dStar) := by
    intro hds
    by_cases hm3 : c.mode = 3
    · have hgt1 : ¬ (c.dStar ≤ 1) := by intro hle; simp [hds, hm3, hle] at h3b
      simp only [hm3, beq_self_eq_true, ↓reduceIte]; omega
    · have hm3b : (c.mode == 3) = false := beq_false_of_ne hm3
      have hne0 : c.dStar ≠ 0 := by intro h0; simp [hds, hm3b, h0] at h3b
      simp only [hm3b, Bool.false_eq_true, ↓reduceIte]; omega
  have hcltZ : (c.cLoNum : ℤ) * c.cHiDen < (c.cHiNum : ℤ) * c.cLoDen := by
    have h' : decide ((c.cLoNum : ℤ) * c.cHiDen < (c.cHiNum : ℤ) * c.cLoDen) = true := by
      cases hb : decide ((c.cLoNum : ℤ) * c.cHiDen < (c.cHiNum : ℤ) * c.cLoDen)
      · simp [hb] at h2
      · rfl
    exact decide_eq_true_eq.mp h'
  have hcLoDQ : (0 : ℚ) < (c.cLoDen : ℚ) := by exact_mod_cast hcLoD
  have hcHiDQ : (0 : ℚ) < (c.cHiDen : ℚ) := by exact_mod_cast hcHiD
  have hcltQ : (c.cLoNum : ℚ) / (c.cLoDen : ℚ) < (c.cHiNum : ℚ) / (c.cHiDen : ℚ) := by
    rw [div_lt_div_iff₀ hcLoDQ hcHiDQ]; exact_mod_cast hcltZ
  set dh2 : ℕ := c.d2 - c.dg
  set dh1 : ℕ := c.d1 - c.dg
  set dStarEff : ℕ := if c.mode == 3 then c.dStar - 1 else c.dStar
  set K0 : ℕ := max (if c.hasDStar then c.dStar else 0) (max c.d1 c.d2) + 3
  set mDenNat : ℕ := if c.m == 0 then 1 else c.m * c.m
  set mDen : ℤ := (mDenNat : ℤ)
  have hmDen_eq_orig : mDen = if c.m == 0 then 1 else (c.m : ℤ) * (c.m : ℤ) := by
    dsimp [mDen, mDenNat]; split_ifs <;> simp
  have hmDen_pos : 0 < mDen := by
    rw [hmDen_eq_orig]; split_ifs with hm0
    · norm_num
    · have : 0 < c.m := Nat.pos_of_ne_zero (fun h => by simp [h] at hm0); positivity
  have hmDenQ : (0 : ℚ) < (mDen : ℚ) := by exact_mod_cast hmDen_pos
  have hNQ : (0 : ℚ) < (N : ℚ) := by norm_num [N]
  have hwYQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY, D]
  have hcardIdx : (Fintype.card Idx : ℚ) = (N : ℚ) := by
    have : Fintype.card Idx = N := by simp [Idx, N]
    exact_mod_cast this
  have hds_even : c.mode = 3 → 2 * (dStarEff / 2) = dStarEff := by
    intro hm3
    have hmod : (c.dStar - 1) % 2 = 0 := by by_contra hne; simp [hm3, hne] at h4
    have hde : dStarEff = c.dStar - 1 := by dsimp [dStarEff]; simp [hm3]
    omega
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨hslopeA, hslopeB⟩, hpt⟩, ⟨⟨⟨hep0, hep1⟩, hep2⟩, hep3⟩⟩, hcap⟩
  have hrk_eq : ∀ k0 : ℕ, (c.vx : ℚ) * ((rankDiffNum 2 c.m c.s k0 : ℚ) / (mDen : ℚ)) =
      (c.vx : ℚ) * rankDiffQ 2 c.m c.s k0 := by
    intro k0
    by_cases hm0 : c.m = 0
    · have hvx0 : c.vx = 0 := by by_contra hne; simp [hm0, hne] at h5
      simp [hvx0]
    · have hmpos : 0 < c.m := Nat.pos_of_ne_zero hm0
      have hmne : (c.m == 0) = false := beq_false_of_ne hm0
      have hmDen_eq : (mDen : ℚ) = (c.m : ℚ) * (c.m : ℚ) := by rw [hmDen_eq_orig]; simp [hmne]
      rw [hmDen_eq, rankDiffNum_div_eq 2 c.m c.s k0 hmpos]
  -- Pointwise bound for ALL (k0, rr0) with rr0 ≤ 2 * k0!
  have hpt_le : ∀ k0 ≤ K0, ∀ rr0 ≤ 2 * k0,
      (c.vx : ℚ) * rankDiffQ 2 c.m c.s k0 +
      max (0 : ℚ) ((c.ua : ℚ) - (c.vg : ℚ) * (rr0 : ℚ) -
        (c.vh1 : ℚ) * ((2 * k0 - 1 - rr0 : ℕ) : ℚ) - (c.vh2 : ℚ) * ((2 * k0 - 2 - rr0 : ℕ) : ℚ)) ≤
      (c.unNum : ℚ) / (mDen : ℚ) +
      (c.vlcg : ℚ) * ((rr0 - c.dg : ℕ) : ℚ) +
      (c.vlch1 : ℚ) * ((2 * k0 - 1 - rr0 - dh1 : ℕ) : ℚ) +
      (c.vlch2 : ℚ) * ((2 * k0 - 2 - rr0 - dh2 : ℕ) : ℚ) +
      (if 1 ≤ dh1 ∧ 2 ≤ dh2 then (c.vrh : ℚ) * (resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) : ℚ) else 0) +
      (if c.hasDStar = true then (c.vrf0 : ℚ) * (t3Vrf0Ord c.mode c.dg dStarEff k0 rr0 : ℚ) else 0) +
      (if c.mode = 2 then (c.vh11 : ℚ) * ((2 * k0 - 2 - rr0 : ℕ) : ℚ) else 0) := by
    intro k0 hk0 rr0 hrr0
    set rkN : ℕ := rkDiffNat 2 c.m c.s k0
    set h1 : ℕ := c.ua - (c.vg * rr0 + c.vh1 * (2 * k0 - 1 - rr0) + c.vh2 * (2 * k0 - 2 - rr0))
    set baseSub : ℕ :=
      c.vlcg * (rr0 - c.dg) +
      c.vlch1 * (2 * k0 - 1 - rr0 - dh1) +
      c.vlch2 * (2 * k0 - 2 - rr0 - dh2) +
      (if decide (1 ≤ dh1 ∧ 2 ≤ dh2) && (c.vrh != 0) then
        c.vrh * resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) else 0) +
      (if (c.mode == 2) && (c.vh11 != 0) then c.vh11 * (2 * k0 - 2 - rr0) else 0)
    set subTot : ℕ :=
      c.vlcg * (rr0 - c.dg) +
      c.vlch1 * (2 * k0 - 1 - rr0 - dh1) +
      c.vlch2 * (2 * k0 - 2 - rr0 - dh2) +
      (if 1 ≤ dh1 ∧ 2 ≤ dh2 then c.vrh * resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) else 0) +
      (if c.hasDStar = true then c.vrf0 * t3Vrf0Ord c.mode c.dg dStarEff k0 rr0 else 0) +
      (if c.mode = 2 then c.vh11 * (2 * k0 - 2 - rr0) else 0)
    have hbase_eq : baseSub + (if c.hasDStar = true then c.vrf0 * t3Vrf0Ord c.mode c.dg dStarEff k0 rr0 else 0) = subTot := by
      dsimp only [baseSub, subTot]
      have hrh_eq : (if decide (1 ≤ dh1 ∧ 2 ≤ dh2) && (c.vrh != 0) then
            c.vrh * resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) else 0) =
          (if 1 ≤ dh1 ∧ 2 ≤ dh2 then c.vrh * resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) else 0) := by
        by_cases hp : 1 ≤ dh1 ∧ 2 ≤ dh2
        · by_cases hv : c.vrh = 0 <;> simp [hp, hv]
        · simp [hp]
      have hh11_eq : (if (c.mode == 2) && (c.vh11 != 0) then c.vh11 * (2 * k0 - 2 - rr0) else 0) =
          (if c.mode = 2 then c.vh11 * (2 * k0 - 2 - rr0) else 0) := by
        by_cases hp : c.mode = 2
        · by_cases hv : c.vh11 = 0 <;> simp [hp, hv]
        · simp [hp]
      rw [hrh_eq, hh11_eq]; omega
    have hNat : c.vx * rkN + h1 * mDenNat ≤ c.unNum.toNat + subTot * mDenNat := by
      have hk_ok := (allNat_eq_true_iff _ _).mp hpt k0 (by omega)
      set h1U : ℕ := c.ua - max (min c.vg c.vh1 * (2 * k0 - 1)) (min c.vg (c.vh1 + c.vh2) * (2 * k0 - 2))
      by_cases hU : Nat.ble (c.vx * rkN + h1U * mDenNat) c.unNum.toNat = true
      · have hleU : c.vx * rkN + h1U * mDenNat ≤ c.unNum.toNat := Nat.ble_eq.mp hU
        have hh1_le : h1 ≤ h1U := h1U_ge_h1 c.ua c.vg c.vh1 c.vh2 k0 rr0 hrr0
        have hm := Nat.mul_le_mul_right mDenNat hh1_le
        omega
      · rw [if_neg hU] at hk_ok
        have hrr_ok := (allNat_eq_true_iff _ _).mp hk_ok rr0 (by omega)
        by_cases hB : Nat.ble (c.vx * rkN + h1 * mDenNat) (c.unNum.toNat + baseSub * mDenNat) = true
        · have hleB : c.vx * rkN + h1 * mDenNat ≤ c.unNum.toNat + baseSub * mDenNat := Nat.ble_eq.mp hB
          have hsub_le : baseSub ≤ subTot := by omega
          have hm := Nat.mul_le_mul_right mDenNat hsub_le
          omega
        · simp only [← Bool.and_eq_true] at hrr_ok
          rw [if_neg hB] at hrr_ok
          by_cases hRf : (c.hasDStar && (c.vrf0 != 0)) = true
          · rw [if_pos hRf] at hrr_ok
            have hds : c.hasDStar = true := by simp at hRf; exact hRf.1
            have hrf0_eq : (if Nat.ble (dStarEff + 3) k0 then 2 * c.dg * k0 + dStarEff * rr0 - dStarEff * c.dg
                else t3Vrf0Ord c.mode c.dg dStarEff k0 rr0) = t3Vrf0Ord c.mode c.dg dStarEff k0 rr0 := by
              by_cases hge : Nat.ble (dStarEff + 3) k0 = true
              · rw [if_pos hge]
                exact (t3Vrf0Ord_eq_large c.mode c.dg dStarEff k0 rr0 hdg_pos (hds_pos hds) hdg_even hds_even (Nat.ble_eq.mp hge)).symm
              · rw [if_neg hge]
            rw [hrf0_eq] at hrr_ok
            have hleR := Nat.ble_eq.mp hrr_ok
            have htot_eq : baseSub + c.vrf0 * t3Vrf0Ord c.mode c.dg dStarEff k0 rr0 = subTot := by
              rw [← hbase_eq, if_pos hds]
            rwa [htot_eq] at hleR
          · rw [if_neg hRf] at hrr_ok; cases hrr_ok
    have hZ : ((c.vx : ℤ) * rankDiffNum 2 c.m c.s k0 +
        (max (0 : ℤ) ((c.ua : ℤ) - (c.vg : ℤ) * (rr0 : ℤ) -
            (c.vh1 : ℤ) * ((2 * k0 - 1 - rr0 : ℕ) : ℤ) - (c.vh2 : ℤ) * ((2 * k0 - 2 - rr0 : ℕ) : ℤ)) -
          (c.vlcg : ℤ) * ((rr0 - c.dg : ℕ) : ℤ) -
          (c.vlch1 : ℤ) * ((2 * k0 - 1 - rr0 - dh1 : ℕ) : ℤ) -
          (c.vlch2 : ℤ) * ((2 * k0 - 2 - rr0 - dh2 : ℕ) : ℤ) -
          (if 1 ≤ dh1 ∧ 2 ≤ dh2 then (c.vrh : ℤ) * (resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) : ℤ) else 0) -
          (if c.hasDStar = true then (c.vrf0 : ℤ) * (t3Vrf0Ord c.mode c.dg dStarEff k0 rr0 : ℤ) else 0) -
          (if c.mode = 2 then (c.vh11 : ℤ) * ((2 * k0 - 2 - rr0 : ℕ) : ℤ) else 0)) * mDen : ℚ) ≤
        (c.unNum : ℚ) := by
      have hNatZ : (c.vx : ℤ) * (rkN : ℤ) + (h1 : ℤ) * mDen ≤ c.unNum + (subTot : ℤ) * mDen := by
        have h' : ((c.vx * rkN + h1 * mDenNat : ℕ) : ℤ) ≤ ((c.unNum.toNat + subTot * mDenNat : ℕ) : ℤ) := by
          exact_mod_cast hNat
        push_cast at h'
        rwa [hun_toNat] at h'
      have hrkZ : (rkN : ℤ) = rankDiffNum 2 c.m c.s k0 := rkDiffNat_cast 2 c.m c.s k0
      have hh1Z : (h1 : ℤ) = max (0 : ℤ) ((c.ua : ℤ) - (c.vg : ℤ) * (rr0 : ℤ) -
          (c.vh1 : ℤ) * ((2 * k0 - 1 - rr0 : ℕ) : ℤ) - (c.vh2 : ℤ) * ((2 * k0 - 2 - rr0 : ℕ) : ℤ)) := by
        dsimp only [h1]; rw [nat_sub_cast_eq_max_zero]; congr 1; push_cast; ring
      have hsubZ : (subTot : ℤ) =
          (c.vlcg : ℤ) * ((rr0 - c.dg : ℕ) : ℤ) +
          (c.vlch1 : ℤ) * ((2 * k0 - 1 - rr0 - dh1 : ℕ) : ℤ) +
          (c.vlch2 : ℤ) * ((2 * k0 - 2 - rr0 - dh2 : ℕ) : ℤ) +
          (if 1 ≤ dh1 ∧ 2 ≤ dh2 then (c.vrh : ℤ) * (resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) : ℤ) else 0) +
          (if c.hasDStar = true then (c.vrf0 : ℤ) * (t3Vrf0Ord c.mode c.dg dStarEff k0 rr0 : ℤ) else 0) +
          (if c.mode = 2 then (c.vh11 : ℤ) * ((2 * k0 - 2 - rr0 : ℕ) : ℤ) else 0) := by
        simp only [subTot, Nat.cast_add, Nat.cast_mul, Nat.cast_ite, Nat.cast_zero]
      have hb' : (c.vx : ℤ) * rankDiffNum 2 c.m c.s k0 +
          (max (0 : ℤ) ((c.ua : ℤ) - (c.vg : ℤ) * (rr0 : ℤ) -
              (c.vh1 : ℤ) * ((2 * k0 - 1 - rr0 : ℕ) : ℤ) - (c.vh2 : ℤ) * ((2 * k0 - 2 - rr0 : ℕ) : ℤ)) -
            (c.vlcg : ℤ) * ((rr0 - c.dg : ℕ) : ℤ) -
            (c.vlch1 : ℤ) * ((2 * k0 - 1 - rr0 - dh1 : ℕ) : ℤ) -
            (c.vlch2 : ℤ) * ((2 * k0 - 2 - rr0 - dh2 : ℕ) : ℤ) -
            (if 1 ≤ dh1 ∧ 2 ≤ dh2 then (c.vrh : ℤ) * (resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) : ℤ) else 0) -
            (if c.hasDStar = true then (c.vrf0 : ℤ) * (t3Vrf0Ord c.mode c.dg dStarEff k0 rr0 : ℤ) else 0) -
            (if c.mode = 2 then (c.vh11 : ℤ) * ((2 * k0 - 2 - rr0 : ℕ) : ℤ) else 0)) * mDen ≤ c.unNum := by
        rw [hrkZ, hh1Z, hsubZ] at hNatZ
        linarith
      exact_mod_cast hb'
    push_cast [Int.cast_max] at hZ
    have hQ : (c.vx : ℚ) * (rankDiffNum 2 c.m c.s k0 : ℚ) +
        (max (0 : ℚ) ((c.ua : ℚ) - (c.vg : ℚ) * (rr0 : ℚ) -
            (c.vh1 : ℚ) * ((2 * k0 - 1 - rr0 : ℕ) : ℚ) - (c.vh2 : ℚ) * ((2 * k0 - 2 - rr0 : ℕ) : ℚ)) -
          (c.vlcg : ℚ) * ((rr0 - c.dg : ℕ) : ℚ) -
          (c.vlch1 : ℚ) * ((2 * k0 - 1 - rr0 - dh1 : ℕ) : ℚ) -
          (c.vlch2 : ℚ) * ((2 * k0 - 2 - rr0 - dh2 : ℕ) : ℚ) -
          (if 1 ≤ dh1 ∧ 2 ≤ dh2 then (c.vrh : ℚ) * (resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) : ℚ) else 0) -
          (if c.hasDStar = true then (c.vrf0 : ℚ) * (t3Vrf0Ord c.mode c.dg dStarEff k0 rr0 : ℚ) else 0) -
          (if c.mode = 2 then (c.vh11 : ℚ) * ((2 * k0 - 2 - rr0 : ℕ) : ℚ) else 0)) * (mDen : ℚ) ≤
        (c.unNum : ℚ) := by
      split_ifs at hZ ⊢ <;> linarith
    rw [← hrk_eq k0]
    have hdiv := div_le_div_of_nonneg_right hQ hmDenQ.le
    rw [add_div, mul_div_assoc, mul_div_cancel_right₀ _ hmDenQ.ne'] at hdiv
    linarith
  -- Slope inequalities in ℚ!
  have hslA : (c.vx : ℚ) * (rankDiffQ 2 c.m c.s K0 - rankDiffQ 2 c.m c.s (K0 - 1)) ≤
      2 * (c.vlch1 : ℚ) + 2 * (c.vlch2 : ℚ) +
      (if 1 ≤ dh1 ∧ 2 ≤ dh2 then 2 * ((dh1 : ℚ) + (dh2 : ℚ)) * (c.vrh : ℚ) else 0) +
      (if c.hasDStar = true then 2 * (c.dg : ℚ) * (c.vrf0 : ℚ) else 0) +
      (if c.mode = 2 then 2 * (c.vh11 : ℚ) else 0) := by
    have hZ : ((c.vx : ℤ) * (rankDiffNum 2 c.m c.s K0 - rankDiffNum 2 c.m c.s (K0 - 1)) : ℚ) ≤
        ((2 * (c.vlch1 : ℤ) + 2 * (c.vlch2 : ℤ) +
          (if 1 ≤ dh1 ∧ 2 ≤ dh2 then 2 * ((dh1 : ℤ) + (dh2 : ℤ)) * (c.vrh : ℤ) else 0) +
          (if c.hasDStar = true then 2 * (c.dg : ℤ) * (c.vrf0 : ℤ) else 0) +
          (if c.mode = 2 then 2 * (c.vh11 : ℤ) else 0)) * mDen : ℚ) := by
      exact_mod_cast (by simpa [dh1, dh2, decide_eq_true_eq, beq_iff_eq] using decide_eq_true_eq.mp hslopeA)
    push_cast at hZ
    have hdiv := div_le_div_of_nonneg_right (show (c.vx : ℚ) * ((rankDiffNum 2 c.m c.s K0 : ℚ) - (rankDiffNum 2 c.m c.s (K0 - 1) : ℚ)) ≤
        (2 * (c.vlch1 : ℚ) + 2 * (c.vlch2 : ℚ) +
          (if 1 ≤ dh1 ∧ 2 ≤ dh2 then 2 * ((dh1 : ℚ) + (dh2 : ℚ)) * (c.vrh : ℚ) else 0) +
          (if c.hasDStar = true then 2 * (c.dg : ℚ) * (c.vrf0 : ℚ) else 0) +
          (if c.mode = 2 then 2 * (c.vh11 : ℚ) else 0)) * (mDen : ℚ) by split_ifs at hZ ⊢ <;> linarith) hmDenQ.le
    rw [mul_div_cancel_right₀ _ hmDenQ.ne'] at hdiv
    have h3 : (c.vx : ℚ) * ((rankDiffNum 2 c.m c.s K0 : ℚ) - (rankDiffNum 2 c.m c.s (K0 - 1) : ℚ)) / (mDen : ℚ) =
        (c.vx : ℚ) * (rankDiffQ 2 c.m c.s K0 - rankDiffQ 2 c.m c.s (K0 - 1)) := by
      rw [mul_sub, sub_div, mul_div_assoc, mul_div_assoc, hrk_eq K0, hrk_eq (K0 - 1), ← mul_sub]
    linarith
  have hslB : (c.vx : ℚ) * (rankDiffQ 2 c.m c.s K0 - rankDiffQ 2 c.m c.s (K0 - 1)) ≤
      2 * (c.vlcg : ℚ) +
      (if c.hasDStar = true then 2 * ((c.dg : ℚ) + (dStarEff : ℚ)) * (c.vrf0 : ℚ) else 0) := by
    have hZ : ((c.vx : ℤ) * (rankDiffNum 2 c.m c.s K0 - rankDiffNum 2 c.m c.s (K0 - 1)) : ℚ) ≤
        ((2 * (c.vlcg : ℤ) +
          (if c.hasDStar = true then 2 * ((c.dg : ℤ) + (dStarEff : ℤ)) * (c.vrf0 : ℤ) else 0)) * mDen : ℚ) := by
      exact_mod_cast (by simpa [dStarEff, decide_eq_true_eq] using decide_eq_true_eq.mp hslopeB)
    push_cast at hZ
    have hdiv := div_le_div_of_nonneg_right (show (c.vx : ℚ) * ((rankDiffNum 2 c.m c.s K0 : ℚ) - (rankDiffNum 2 c.m c.s (K0 - 1) : ℚ)) ≤
        (2 * (c.vlcg : ℚ) + (if c.hasDStar = true then 2 * ((c.dg : ℚ) + (dStarEff : ℚ)) * (c.vrf0 : ℚ) else 0)) * (mDen : ℚ) by
      split_ifs at hZ ⊢ <;> linarith) hmDenQ.le
    rw [mul_div_cancel_right₀ _ hmDenQ.ne'] at hdiv
    have h3 : (c.vx : ℚ) * ((rankDiffNum 2 c.m c.s K0 : ℚ) - (rankDiffNum 2 c.m c.s (K0 - 1) : ℚ)) / (mDen : ℚ) =
        (c.vx : ℚ) * (rankDiffQ 2 c.m c.s K0 - rankDiffQ 2 c.m c.s (K0 - 1)) := by
      rw [mul_sub, sub_div, mul_div_assoc, mul_div_assoc, hrk_eq K0, hrk_eq (K0 - 1), ← mul_sub]
    linarith
  -- Extend pointwise bound to ALL (k0, rr0) with rr0 ≤ 2*k0 via the exact 2-ray decomposition!
  have hpt_all : ∀ (k0 rr0 : ℕ) (hrr0 : rr0 ≤ 2 * k0) (α : ℚ), (α = 0 ∨ α = 1) →
      (c.vx : ℚ) * rankDiffQ 2 c.m c.s k0 + (c.ua : ℚ) * α ≤
      (c.unNum : ℚ) / (mDen : ℚ) +
      (c.vg : ℚ) * (α * (rr0 : ℚ)) + (c.vh1 : ℚ) * (α * ((2 * k0 - 1 - rr0 : ℕ) : ℚ)) + (c.vh2 : ℚ) * (α * ((2 * k0 - 2 - rr0 : ℕ) : ℚ)) +
      (c.vlcg : ℚ) * ((rr0 - c.dg : ℕ) : ℚ) +
      (c.vlch1 : ℚ) * ((2 * k0 - 1 - rr0 - dh1 : ℕ) : ℚ) +
      (c.vlch2 : ℚ) * ((2 * k0 - 2 - rr0 - dh2 : ℕ) : ℚ) +
      (if 1 ≤ dh1 ∧ 2 ≤ dh2 then (c.vrh : ℚ) * (resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) : ℚ) else 0) +
      (if c.hasDStar = true then (c.vrf0 : ℚ) * (t3Vrf0Ord c.mode c.dg dStarEff k0 rr0 : ℚ) else 0) +
      (if c.mode = 2 then (c.vh11 : ℚ) * ((2 * k0 - 2 - rr0 : ℕ) : ℚ) else 0) := by
    intro k0 rr0 hrr0 α hα
    have hα_max : (c.ua : ℚ) * α - (c.vg : ℚ) * (α * (rr0 : ℚ)) -
        (c.vh1 : ℚ) * (α * ((2 * k0 - 1 - rr0 : ℕ) : ℚ)) - (c.vh2 : ℚ) * (α * ((2 * k0 - 2 - rr0 : ℕ) : ℚ)) ≤
        max (0 : ℚ) ((c.ua : ℚ) - (c.vg : ℚ) * (rr0 : ℚ) -
          (c.vh1 : ℚ) * ((2 * k0 - 1 - rr0 : ℕ) : ℚ) - (c.vh2 : ℚ) * ((2 * k0 - 2 - rr0 : ℕ) : ℚ)) := by
      rcases hα with rfl | rfl
      · simp only [mul_zero, zero_mul, sub_zero, le_max_left]
      · simp only [mul_one, one_mul, le_max_right]
    by_cases hk0 : k0 ≤ K0
    · linarith [hpt_le k0 hk0 rr0 hrr0]
    · have hgt : K0 ≤ k0 := by omega
      set M : ℕ := max (dh1 + 1) (dh2 + 2)
      have hdgM : c.dg + M ≤ 2 * K0 := by dsimp [M, K0, dh1, dh2]; omega
      -- Choose base point rB ≤ 2 * K0 so every growing coordinate is already past its hinge!
      set rB : ℕ :=
        if rr0 ≤ c.dg then rr0
        else if 2 * k0 - rr0 ≤ M then 2 * K0 - (2 * k0 - rr0)
        else min rr0 (2 * K0 - M)
      have hrB_le : rB ≤ 2 * K0 := by dsimp [rB]; split_ifs <;> omega
      have hrB_le_rr : rB ≤ rr0 := by dsimp [rB]; split_ifs <;> omega
      have hrem_le : 2 * K0 - rB ≤ 2 * k0 - rr0 := by dsimp [rB]; split_ifs <;> omega
      set q : ℕ := rr0 - rB
      set p : ℕ := (2 * k0 - rr0) - (2 * K0 - rB)
      have hpq : p + q = 2 * (k0 - K0) := by omega
      have hp_hinge : 0 < p → M ≤ 2 * K0 - rB := by dsimp [p, rB]; split_ifs <;> omega
      have hq_hinge : 0 < q → c.dg ≤ rB := by dsimp [q, rB]; split_ifs <;> omega
      have hbase := hpt_le K0 le_rfl rB hrB_le
      have hmax_mono : max (0 : ℚ) ((c.ua : ℚ) - (c.vg : ℚ) * (rr0 : ℚ) -
            (c.vh1 : ℚ) * ((2 * k0 - 1 - rr0 : ℕ) : ℚ) - (c.vh2 : ℚ) * ((2 * k0 - 2 - rr0 : ℕ) : ℚ)) ≤
          max (0 : ℚ) ((c.ua : ℚ) - (c.vg : ℚ) * (rB : ℚ) -
            (c.vh1 : ℚ) * ((2 * K0 - 1 - rB : ℕ) : ℚ) - (c.vh2 : ℚ) * ((2 * K0 - 2 - rB : ℕ) : ℚ)) := by
        apply max_le (le_max_left _ _)
        refine le_trans ?_ (le_max_right _ _)
        have h1 : (rB : ℚ) ≤ (rr0 : ℚ) := by exact_mod_cast hrB_le_rr
        have h2 : ((2 * K0 - 1 - rB : ℕ) : ℚ) ≤ ((2 * k0 - 1 - rr0 : ℕ) : ℚ) := by exact_mod_cast (by omega : 2 * K0 - 1 - rB ≤ 2 * k0 - 1 - rr0)
        have h3 : ((2 * K0 - 2 - rB : ℕ) : ℚ) ≤ ((2 * k0 - 2 - rr0 : ℕ) : ℚ) := by exact_mod_cast (by omega : 2 * K0 - 2 - rB ≤ 2 * k0 - 2 - rr0)
        have hm1 := mul_le_mul_of_nonneg_left h1 (show (0 : ℚ) ≤ (c.vg : ℚ) by positivity)
        have hm2 := mul_le_mul_of_nonneg_left h2 (show (0 : ℚ) ≤ (c.vh1 : ℚ) by positivity)
        have hm3 := mul_le_mul_of_nonneg_left h3 (show (0 : ℚ) ≤ (c.vh2 : ℚ) by positivity)
        linarith only [hm1, hm2, hm3]
      have htail_rk := rankDiffQ_le_linear_tail 2 c.m c.s K0 k0 (by dsimp [K0]; omega) hgt
      have hstep_split : ((k0 - K0 : ℕ) : ℚ) = (p : ℚ) / 2 + (q : ℚ) / 2 := by
        have : (p : ℚ) + (q : ℚ) = 2 * ((k0 - K0 : ℕ) : ℚ) := by exact_mod_cast hpq
        linarith
      -- Check growth of every single term along (p, q)!
      have hlcg_g : ((rB - c.dg : ℕ) : ℚ) + (q : ℚ) ≤ ((rr0 - c.dg : ℕ) : ℚ) := by
        by_cases hq0 : q = 0
        · rw [hq0, Nat.cast_zero, add_zero]; exact_mod_cast (by omega : rB - c.dg ≤ rr0 - c.dg)
        · have hdg_rB := hq_hinge (Nat.pos_of_ne_zero hq0)
          exact_mod_cast (by omega : (rB - c.dg) + q ≤ rr0 - c.dg)
      have hlch1_g : ((2 * K0 - 1 - rB - dh1 : ℕ) : ℚ) + (p : ℚ) ≤ ((2 * k0 - 1 - rr0 - dh1 : ℕ) : ℚ) := by
        by_cases hp0 : p = 0
        · rw [hp0, Nat.cast_zero, add_zero]; exact_mod_cast (by omega : 2 * K0 - 1 - rB - dh1 ≤ 2 * k0 - 1 - rr0 - dh1)
        · have hM_rB := hp_hinge (Nat.pos_of_ne_zero hp0)
          exact_mod_cast (by dsimp [M] at hM_rB; omega : (2 * K0 - 1 - rB - dh1) + p ≤ 2 * k0 - 1 - rr0 - dh1)
      have hlch2_g : ((2 * K0 - 2 - rB - dh2 : ℕ) : ℚ) + (p : ℚ) ≤ ((2 * k0 - 2 - rr0 - dh2 : ℕ) : ℚ) := by
        by_cases hp0 : p = 0
        · rw [hp0, Nat.cast_zero, add_zero]; exact_mod_cast (by omega : 2 * K0 - 2 - rB - dh2 ≤ 2 * k0 - 2 - rr0 - dh2)
        · have hM_rB := hp_hinge (Nat.pos_of_ne_zero hp0)
          exact_mod_cast (by dsimp [M] at hM_rB; omega : (2 * K0 - 2 - rB - dh2) + p ≤ 2 * k0 - 2 - rr0 - dh2)
      have hh11_g : ((2 * K0 - 2 - rB : ℕ) : ℚ) + (p : ℚ) ≤ ((2 * k0 - 2 - rr0 : ℕ) : ℚ) := by
        by_cases hp0 : p = 0
        · rw [hp0, Nat.cast_zero, add_zero]; exact_mod_cast (by omega : 2 * K0 - 2 - rB ≤ 2 * k0 - 2 - rr0)
        · have hM_rB := hp_hinge (Nat.pos_of_ne_zero hp0)
          exact_mod_cast (by dsimp [M] at hM_rB; omega : (2 * K0 - 2 - rB) + p ≤ 2 * k0 - 2 - rr0)
      have hrh_g : (if 1 ≤ dh1 ∧ 2 ≤ dh2 then
          (c.vrh : ℚ) * (resOrdExact dh1 (2 * K0 - 1 - rB) dh2 (2 * K0 - 2 - rB) : ℚ) +
          ((dh1 : ℚ) + (dh2 : ℚ)) * (c.vrh : ℚ) * (p : ℚ) else 0) ≤
          (if 1 ≤ dh1 ∧ 2 ≤ dh2 then (c.vrh : ℚ) * (resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) : ℚ) else 0) := by
        split_ifs with hr
        · by_cases hp0 : p = 0
          · have h1 : 2 * k0 - 1 - rr0 = 2 * K0 - 1 - rB := by omega
            have h2 : 2 * k0 - 2 - rr0 = 2 * K0 - 2 - rB := by omega
            rw [hp0, h1, h2, Nat.cast_zero, mul_zero, add_zero]
          · have hM_rB := hp_hinge (Nat.pos_of_ne_zero hp0)
            have hre : resOrdExact dh1 (2 * K0 - 1 - rB) dh2 (2 * K0 - 2 - rB) + (dh1 + dh2) * p ≤
                resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) := by
              unfold resOrdExact
              have hd1ne : dh1 ≠ 0 := by omega
              have hd2ne : dh2 ≠ 0 := by omega
              simp only [hd1ne, hd2ne, ↓reduceIte]
              have hd1_leK : dh1 ≤ 2 * K0 - 1 - rB := by dsimp [M] at hM_rB; omega
              have hd2_leK : dh2 ≤ 2 * K0 - 2 - rB := by dsimp [M] at hM_rB; omega
              have hd1_lek : dh1 ≤ 2 * k0 - 1 - rr0 := by omega
              have hd2_lek : dh2 ≤ 2 * k0 - 2 - rr0 := by omega
              have hza : dh1 - (2 * K0 - 1 - rB) = 0 := by omega
              have hzb : dh2 - (2 * K0 - 2 - rB) = 0 := by omega
              have hzc : dh1 - (2 * k0 - 1 - rr0) = 0 := by omega
              have hzd : dh2 - (2 * k0 - 2 - rr0) = 0 := by omega
              rw [hza, hzb, hzc, hzd, Nat.zero_mul, Nat.add_zero, Nat.add_zero]
              have hle1 : dh1 * dh2 ≤ dh2 * (2 * K0 - 1 - rB) + dh1 * (2 * K0 - 2 - rB) := by
                have h1 : dh1 ≤ 2 * K0 - 1 - rB := by omega
                have h2 : dh2 ≤ 2 * K0 - 2 - rB := by omega
                nlinarith only [h1, h2]
              have hle2 : dh1 * dh2 ≤ dh2 * (2 * k0 - 1 - rr0) + dh1 * (2 * k0 - 2 - rr0) := by
                have h1 : dh1 ≤ 2 * k0 - 1 - rr0 := by omega
                have h2 : dh2 ≤ 2 * k0 - 2 - rr0 := by omega
                nlinarith only [h1, h2]
              have hp1 : (2 * K0 - 1 - rB) + p = 2 * k0 - 1 - rr0 := by dsimp [M] at hM_rB; omega
              have hp2 : (2 * K0 - 2 - rB) + p = 2 * k0 - 2 - rr0 := by dsimp [M] at hM_rB; omega
              zify [hle1, hle2]
              have hp1Z : ((2 * K0 - 1 - rB : ℕ) : ℤ) + (p : ℤ) = ((2 * k0 - 1 - rr0 : ℕ) : ℤ) := by exact_mod_cast hp1
              have hp2Z : ((2 * K0 - 2 - rB : ℕ) : ℤ) + (p : ℤ) = ((2 * k0 - 2 - rr0 : ℕ) : ℤ) := by exact_mod_cast hp2
              have heqZ : ((dh2 : ℤ) * ((2 * K0 - 1 - rB : ℕ) : ℤ) + (dh1 : ℤ) * ((2 * K0 - 2 - rB : ℕ) : ℤ) - (dh1 : ℤ) * (dh2 : ℤ)) +
                  ((dh1 : ℤ) + (dh2 : ℤ)) * (p : ℤ) =
                  (dh2 : ℤ) * ((2 * k0 - 1 - rr0 : ℕ) : ℤ) + (dh1 : ℤ) * ((2 * k0 - 2 - rr0 : ℕ) : ℤ) - (dh1 : ℤ) * (dh2 : ℤ) := by
                linear_combination (dh2 : ℤ) * hp1Z + (dh1 : ℤ) * hp2Z
              linarith only [heqZ]
            have hreQ : (resOrdExact dh1 (2 * K0 - 1 - rB) dh2 (2 * K0 - 2 - rB) : ℚ) +
                ((dh1 : ℚ) + (dh2 : ℚ)) * (p : ℚ) ≤
                (resOrdExact dh1 (2 * k0 - 1 - rr0) dh2 (2 * k0 - 2 - rr0) : ℚ) := by exact_mod_cast hre
            have hmul := mul_le_mul_of_nonneg_left hreQ (show (0 : ℚ) ≤ (c.vrh : ℚ) by positivity)
            linarith only [hmul]
        · exact le_rfl
      have hrf0_g : (if c.hasDStar = true then
          (c.vrf0 : ℚ) * (t3Vrf0Ord c.mode c.dg dStarEff K0 rB : ℚ) +
          ((c.dg : ℚ) * (p : ℚ) + ((c.dg : ℚ) + (dStarEff : ℚ)) * (q : ℚ)) * (c.vrf0 : ℚ) else 0) ≤
          (if c.hasDStar = true then (c.vrf0 : ℚ) * (t3Vrf0Ord c.mode c.dg dStarEff k0 rr0 : ℚ) else 0) := by
        split_ifs with hds
        · have hK_ds : dStarEff + 3 ≤ K0 := by dsimp [K0, dStarEff]; rw [if_pos hds]; split_ifs <;> omega
          have h1 := t3Vrf0Ord_eq_large c.mode c.dg dStarEff K0 rB hdg_pos (hds_pos hds) hdg_even hds_even hK_ds
          have h2 := t3Vrf0Ord_eq_large c.mode c.dg dStarEff k0 rr0 hdg_pos (hds_pos hds) hdg_even hds_even (by omega)
          rw [h1, h2]
          have hle1 : dStarEff * c.dg ≤ 2 * c.dg * K0 + dStarEff * rB := by nlinarith only [hK_ds]
          have hle2 : dStarEff * c.dg ≤ 2 * c.dg * k0 + dStarEff * rr0 := by nlinarith only [hK_ds, hgt]
          have heq : (2 * c.dg * K0 + dStarEff * rB - dStarEff * c.dg) +
              (c.dg * p + (c.dg + dStarEff) * q) = 2 * c.dg * k0 + dStarEff * rr0 - dStarEff * c.dg := by
            zify [hle1, hle2]
            have hqZ : (q : ℤ) = (rr0 : ℤ) - (rB : ℤ) := by omega
            have hpqZ : (p : ℤ) + (q : ℤ) = 2 * ((k0 : ℤ) - (K0 : ℤ)) := by omega
            linear_combination (c.dg : ℤ) * hpqZ + (dStarEff : ℤ) * hqZ
          have heqQ : ((2 * c.dg * K0 + dStarEff * rB - dStarEff * c.dg : ℕ) : ℚ) +
              ((c.dg : ℚ) * (p : ℚ) + ((c.dg : ℚ) + (dStarEff : ℚ)) * (q : ℚ)) =
              ((2 * c.dg * k0 + dStarEff * rr0 - dStarEff * c.dg : ℕ) : ℚ) := by exact_mod_cast heq
          have hmul := congrArg ((c.vrf0 : ℚ) * ·) heqQ
          linarith only [hmul]
        · exact le_rfl
      have hp_nn : (0 : ℚ) ≤ (p : ℚ) / 2 := by positivity
      have hq_nn : (0 : ℚ) ≤ (q : ℚ) / 2 := by positivity
      have hvx_nn : (0 : ℚ) ≤ (c.vx : ℚ) := by positivity
      have hcomb_sl : (c.vx : ℚ) * (rankDiffQ 2 c.m c.s K0 - rankDiffQ 2 c.m c.s (K0 - 1)) * ((k0 - K0 : ℕ) : ℚ) ≤
          (c.vlcg : ℚ) * (q : ℚ) + (c.vlch1 : ℚ) * (p : ℚ) + (c.vlch2 : ℚ) * (p : ℚ) +
          (if 1 ≤ dh1 ∧ 2 ≤ dh2 then ((dh1 : ℚ) + (dh2 : ℚ)) * (c.vrh : ℚ) * (p : ℚ) else 0) +
          (if c.hasDStar = true then ((c.dg : ℚ) * (p : ℚ) + ((c.dg : ℚ) + (dStarEff : ℚ)) * (q : ℚ)) * (c.vrf0 : ℚ) else 0) +
          (if c.mode = 2 then (c.vh11 : ℚ) * (p : ℚ) else 0) := by
        rw [hstep_split]
        have hA := mul_le_mul_of_nonneg_right hslA hp_nn
        have hB := mul_le_mul_of_nonneg_right hslB hq_nn
        split_ifs at hA hB ⊢ <;> linarith
      have hrk_mul := mul_le_mul_of_nonneg_left htail_rk hvx_nn
      have h1 := mul_le_mul_of_nonneg_left hlcg_g (show (0 : ℚ) ≤ (c.vlcg : ℚ) by positivity)
      have h2 := mul_le_mul_of_nonneg_left hlch1_g (show (0 : ℚ) ≤ (c.vlch1 : ℚ) by positivity)
      have h3 := mul_le_mul_of_nonneg_left hlch2_g (show (0 : ℚ) ≤ (c.vlch2 : ℚ) by positivity)
      have h4 : (if c.mode = 2 then (c.vh11 : ℚ) * ((2 * K0 - 2 - rB : ℕ) : ℚ) + (c.vh11 : ℚ) * (p : ℚ) else 0) ≤
          (if c.mode = 2 then (c.vh11 : ℚ) * ((2 * k0 - 2 - rr0 : ℕ) : ℚ) else 0) := by
        split_ifs
        · have := mul_le_mul_of_nonneg_left hh11_g (show (0 : ℚ) ≤ (c.vh11 : ℚ) by positivity); linarith
        · exact le_rfl
      split_ifs at hbase hcomb_sl h4 hrh_g hrf0_g ⊢ <;>
        linarith only [hα_max, hbase, hmax_mono, hrk_mul, hcomb_sl, h1, h2, h3, h4, hrh_g, hrf0_g]
  -- Step 2: Sum over i : Idx and divide by N!
  let L (x y : ℚ) : ℚ :=
    (c.unNum : ℚ) / (mDen : ℚ) - (c.ua : ℚ) * ((A : ℚ) / (N : ℚ)) +
    (c.vg : ℚ) * (y * (wY : ℚ) / (N : ℚ)) +
    (c.vh1 : ℚ) * (((x - 1 - y) * (wY : ℚ) + 1) / (N : ℚ)) +
    (c.vh2 : ℚ) * (((x - 2 - y) * (wY : ℚ) + 2) / (N : ℚ)) +
    (c.vlcg : ℚ) * (((y - (c.dg : ℚ)) * (wY : ℚ)) / (N : ℚ)) +
    (c.vlch1 : ℚ) * (((x - 1 - y - (dh1 : ℚ)) * (wY : ℚ) + 1) / (N : ℚ)) +
    (c.vlch2 : ℚ) * (((x - 2 - y - (dh2 : ℚ)) * (wY : ℚ) + 2) / (N : ℚ)) +
    (if 1 ≤ dh1 ∧ 2 ≤ dh2 then
      (c.vrh : ℚ) * ((((dh2 : ℚ) * (x - 1 - y) + (dh1 : ℚ) * (x - 2 - y) - (dh1 : ℚ) * (dh2 : ℚ)) * (wY : ℚ) +
        ((dh2 : ℚ) + 2 * (dh1 : ℚ))) / (N : ℚ)) else 0) +
    (if c.hasDStar = true then
      (c.vrf0 : ℚ) * ((((c.dg : ℚ) * (x - (dStarEff : ℚ)) + (dStarEff : ℚ) * y) * (wY : ℚ)) / (N : ℚ)) else 0) +
    (if c.mode = 2 then (c.vh11 : ℚ) * (((x - 4 - y) * (wY : ℚ) + 1) / (N : ℚ)) else 0)
  have hsum_all : (c.vx : ℚ) * ((∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) / (N : ℚ)) ≤ L cVal cgVal := by
    have hpt_i : ∀ i : Idx,
        (c.vx : ℚ) * rankDiffQ 2 c.m c.s (k i) + (c.ua : ℚ) * (if i ∈ Az then (1 : ℚ) else 0) ≤
        (c.unNum : ℚ) / (mDen : ℚ) +
        (c.vg : ℚ) * ((if i ∈ Az then (1 : ℚ) else 0) * (rr i : ℚ)) +
        (c.vh1 : ℚ) * ((if i ∈ Az then (1 : ℚ) else 0) * ((2 * k i - 1 - rr i : ℕ) : ℚ)) +
        (c.vh2 : ℚ) * ((if i ∈ Az then (1 : ℚ) else 0) * ((2 * k i - 2 - rr i : ℕ) : ℚ)) +
        (c.vlcg : ℚ) * ((rr i - c.dg : ℕ) : ℚ) +
        (c.vlch1 : ℚ) * ((2 * k i - 1 - rr i - dh1 : ℕ) : ℚ) +
        (c.vlch2 : ℚ) * ((2 * k i - 2 - rr i - dh2 : ℕ) : ℚ) +
        (if 1 ≤ dh1 ∧ 2 ≤ dh2 then (c.vrh : ℚ) * (resOrdExact dh1 (2 * k i - 1 - rr i) dh2 (2 * k i - 2 - rr i) : ℚ) else 0) +
        (if c.hasDStar = true then (c.vrf0 : ℚ) * (t3Vrf0Ord c.mode c.dg dStarEff (k i) (rr i) : ℚ) else 0) +
        (if c.mode = 2 then (c.vh11 : ℚ) * ((2 * k i - 2 - rr i : ℕ) : ℚ) else 0) :=
      fun i => hpt_all (k i) (rr i) (hrr_le i) (if i ∈ Az then 1 else 0) (by split_ifs <;> simp)
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt_i i
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hcardIdx] at hsum
    have hAz_sum : (∑ i : Idx, if i ∈ Az then (1 : ℚ) else 0) = (Az.card : ℚ) := by simp [Finset.sum_ite_mem]
    have hg_sum : (∑ i : Idx, (if i ∈ Az then (1 : ℚ) else 0) * (rr i : ℚ)) = ∑ i ∈ Az, (rr i : ℚ) := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    have hh1_sum : (∑ i : Idx, (if i ∈ Az then (1 : ℚ) else 0) * ((2 * k i - 1 - rr i : ℕ) : ℚ)) =
        ∑ i ∈ Az, ((2 * k i - 1 - rr i : ℕ) : ℚ) := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    have hh2_sum : (∑ i : Idx, (if i ∈ Az then (1 : ℚ) else 0) * ((2 * k i - 2 - rr i : ℕ) : ℚ)) =
        ∑ i ∈ Az, ((2 * k i - 2 - rr i : ℕ) : ℚ) := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    rw [hAz_sum, hg_sum, hh1_sum, hh2_sum] at hsum
    have hAzQ : (A : ℚ) ≤ (Az.card : ℚ) := by exact_mod_cast hAz
    have hrh_s : (∑ i : Idx, if 1 ≤ dh1 ∧ 2 ≤ dh2 then
          (c.vrh : ℚ) * (resOrdExact dh1 (2 * k i - 1 - rr i) dh2 (2 * k i - 2 - rr i) : ℚ) else 0) ≤
        (if 1 ≤ dh1 ∧ 2 ≤ dh2 then (c.vrh : ℚ) * (((dh2 : ℚ) * (cVal - 1 - cgVal) + (dh1 : ℚ) * (cVal - 2 - cgVal) -
          (dh1 : ℚ) * (dh2 : ℚ)) * (wY : ℚ) + ((dh2 : ℚ) + 2 * (dh1 : ℚ))) else 0) := by
      split_ifs with hr
      · rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hrh hr) (by positivity)
      · simp
    have hrf0_s : (∑ i : Idx, if c.hasDStar = true then
          (c.vrf0 : ℚ) * (t3Vrf0Ord c.mode c.dg dStarEff (k i) (rr i) : ℚ) else 0) ≤
        (if c.hasDStar = true then (c.vrf0 : ℚ) * (((c.dg : ℚ) * (cVal - (dStarEff : ℚ)) + (dStarEff : ℚ) * cgVal) * (wY : ℚ)) else 0) := by
      split_ifs with hds
      · rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hrf0 hds) (by positivity)
      · simp
    have hh11_s : (∑ i : Idx, if c.mode = 2 then (c.vh11 : ℚ) * ((2 * k i - 2 - rr i : ℕ) : ℚ) else 0) ≤
        (if c.mode = 2 then (c.vh11 : ℚ) * ((cVal - 4 - cgVal) * (wY : ℚ) + 1) else 0) := by
      split_ifs with hm2
      · rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hh11 hm2) (by positivity)
      · simp
    have hcomb : (c.vx : ℚ) * (∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) ≤ (N : ℚ) * L cVal cgVal := by
      have hNL : (N : ℚ) * L cVal cgVal =
          (N : ℚ) * ((c.unNum : ℚ) / (mDen : ℚ)) - (c.ua : ℚ) * (A : ℚ) +
          (c.vg : ℚ) * (cgVal * (wY : ℚ)) +
          (c.vh1 : ℚ) * ((cVal - 1 - cgVal) * (wY : ℚ) + 1) +
          (c.vh2 : ℚ) * ((cVal - 2 - cgVal) * (wY : ℚ) + 2) +
          (c.vlcg : ℚ) * ((cgVal - (c.dg : ℚ)) * (wY : ℚ)) +
          (c.vlch1 : ℚ) * ((cVal - 1 - cgVal - (dh1 : ℚ)) * (wY : ℚ) + 1) +
          (c.vlch2 : ℚ) * ((cVal - 2 - cgVal - (dh2 : ℚ)) * (wY : ℚ) + 2) +
          (if 1 ≤ dh1 ∧ 2 ≤ dh2 then
            (c.vrh : ℚ) * (((dh2 : ℚ) * (cVal - 1 - cgVal) + (dh1 : ℚ) * (cVal - 2 - cgVal) - (dh1 : ℚ) * (dh2 : ℚ)) * (wY : ℚ) +
              ((dh2 : ℚ) + 2 * (dh1 : ℚ))) else 0) +
          (if c.hasDStar = true then
            (c.vrf0 : ℚ) * (((c.dg : ℚ) * (cVal - (dStarEff : ℚ)) + (dStarEff : ℚ) * cgVal) * (wY : ℚ)) else 0) +
          (if c.mode = 2 then (c.vh11 : ℚ) * ((cVal - 4 - cgVal) * (wY : ℚ) + 1) else 0) := by
        have hmN : ∀ a b : ℚ, (N : ℚ) * (a * (b / (N : ℚ))) = a * b := fun a b => by
          rw [← mul_assoc, mul_comm (N : ℚ) a, mul_assoc, mul_div_cancel₀ _ hNQ.ne']
        dsimp only [L]; simp only [mul_add, mul_sub, mul_ite, mul_zero, hmN]
      rw [hNL]
      have ha := mul_le_mul_of_nonneg_left hAzQ (show (0 : ℚ) ≤ (c.ua : ℚ) by positivity)
      have h1 := mul_le_mul_of_nonneg_left hg (show (0 : ℚ) ≤ (c.vg : ℚ) by positivity)
      have h2 := mul_le_mul_of_nonneg_left hh1 (show (0 : ℚ) ≤ (c.vh1 : ℚ) by positivity)
      have h3 := mul_le_mul_of_nonneg_left hh2 (show (0 : ℚ) ≤ (c.vh2 : ℚ) by positivity)
      have h4 := mul_le_mul_of_nonneg_left hlcg (show (0 : ℚ) ≤ (c.vlcg : ℚ) by positivity)
      have h5 := mul_le_mul_of_nonneg_left hlch1 (show (0 : ℚ) ≤ (c.vlch1 : ℚ) by positivity)
      have h6 := mul_le_mul_of_nonneg_left hlch2 (show (0 : ℚ) ≤ (c.vlch2 : ℚ) by positivity)
      linarith only [hsum, ha, h1, h2, h3, h4, h5, h6, hrh_s, hrf0_s, hh11_s]
    rw [← mul_div_assoc, div_le_iff₀' hNQ]
    exact hcomb
  -- Step 3: Decode 4 corners + bilinear interpolation!
  have hL_corner : ∀ (cNum cDen cgNum cgDen : ℕ) (hcD : 0 < cDen) (hcgD : 0 < cgDen),
      checkT3Corner c cNum cDen cgNum cgDen = true →
      (c.m = 0 → L ((cNum : ℚ) / (cDen : ℚ)) ((cgNum : ℚ) / (cgDen : ℚ)) < 0) ∧
      (0 < c.m → L ((cNum : ℚ) / (cDen : ℚ)) ((cgNum : ℚ) / (cgDen : ℚ)) -
          (c.vx : ℚ) * vquotLbQ 2 c.m c.s ((cNum : ℚ) / (cDen : ℚ)) <
        -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ))) := by
    intro cNum cDen cgNum cgDen hcD hcgD hep
    have hcDQ : (0 : ℚ) < (cDen : ℚ) := by exact_mod_cast hcD
    have hcgDQ : (0 : ℚ) < (cgDen : ℚ) := by exact_mod_cast hcgD
    unfold checkT3Corner at hep; dsimp only at hep
    set cZ : ℤ := (cNum : ℤ) * (cgDen : ℤ)
    set cgZ : ℤ := (cgNum : ℤ) * (cDen : ℤ)
    set uZ : ℤ := (cDen : ℤ) * (cgDen : ℤ)
    set linZ : ℤ :=
      -(c.ua : ℤ) * (A : ℤ) * uZ +
      (c.vg : ℤ) * (cgZ * (wY : ℤ)) +
      (c.vh1 : ℤ) * ((cZ - uZ - cgZ) * (wY : ℤ) + uZ) +
      (c.vh2 : ℤ) * ((cZ - 2 * uZ - cgZ) * (wY : ℤ) + 2 * uZ) +
      (c.vlcg : ℤ) * ((cgZ - (c.dg : ℤ) * uZ) * (wY : ℤ)) +
      (c.vlch1 : ℤ) * ((cZ - (1 + (dh1 : ℤ)) * uZ - cgZ) * (wY : ℤ) + uZ) +
      (c.vlch2 : ℤ) * ((cZ - (2 + (dh2 : ℤ)) * uZ - cgZ) * (wY : ℤ) + 2 * uZ) +
      (if 1 ≤ dh1 ∧ 2 ≤ dh2 then
        (c.vrh : ℤ) * (((dh2 : ℤ) * (cZ - uZ - cgZ) + (dh1 : ℤ) * (cZ - 2 * uZ - cgZ) -
          (dh1 : ℤ) * (dh2 : ℤ) * uZ) * (wY : ℤ) + ((dh2 : ℤ) + 2 * (dh1 : ℤ)) * uZ) else 0) +
      (if c.hasDStar = true then
        (c.vrf0 : ℤ) * (((c.dg : ℤ) * (cZ - (dStarEff : ℤ) * uZ) + (dStarEff : ℤ) * cgZ) * (wY : ℤ)) else 0) +
      (if c.mode = 2 then (c.vh11 : ℤ) * ((cZ - 4 * uZ - cgZ) * (wY : ℤ) + uZ) else 0)
    have huQ : (uZ : ℚ) = (cDen : ℚ) * (cgDen : ℚ) := by dsimp [uZ]; push_cast; ring
    have hL_eq : L ((cNum : ℚ) / (cDen : ℚ)) ((cgNum : ℚ) / (cgDen : ℚ)) =
        ((c.unNum : ℚ) * (N : ℚ) * (uZ : ℚ) + (linZ : ℚ) * (mDen : ℚ)) / ((N : ℚ) * (mDen : ℚ) * (uZ : ℚ)) := by
      have huPos : (0 : ℚ) < (uZ : ℚ) := by rw [huQ]; positivity
      have huQ_ne : (uZ : ℚ) ≠ 0 := huPos.ne'
      have hc_eq : (cNum : ℚ) / (cDen : ℚ) = (cZ : ℚ) / (uZ : ℚ) := by
        dsimp only [cZ, uZ]; push_cast; field_simp [hcDQ.ne', hcgDQ.ne']
      have hcg_eq : (cgNum : ℚ) / (cgDen : ℚ) = (cgZ : ℚ) / (uZ : ℚ) := by
        dsimp only [cgZ, uZ]; push_cast; field_simp [hcDQ.ne', hcgDQ.ne']
      rw [hc_eq, hcg_eq, eq_div_iff (by positivity)]
      set cQ : ℚ := (cZ : ℚ); set cgQ : ℚ := (cgZ : ℚ); set uQ : ℚ := (uZ : ℚ)
      have hcl : ∀ a b : ℚ, (a * (b / (N : ℚ))) * ((N : ℚ) * (mDen : ℚ) * uQ) = (a * (b * uQ)) * (mDen : ℚ) :=
        fun a b => by field_simp [hNQ.ne']
      have h0 : ((c.unNum : ℚ) / (mDen : ℚ)) * ((N : ℚ) * (mDen : ℚ) * uQ) = (c.unNum : ℚ) * (N : ℚ) * uQ := by
        field_simp [hmDenQ.ne']
      have ha : ((c.ua : ℚ) * ((A : ℚ) / (N : ℚ))) * ((N : ℚ) * (mDen : ℚ) * uQ) = ((c.ua : ℚ) * (A : ℚ) * uQ) * (mDen : ℚ) := by
        rw [hcl]; ring
      have h1 : (cgQ / uQ * (wY : ℚ)) * uQ = cgQ * (wY : ℚ) := by field_simp [huQ_ne]
      have h2 : ((cQ / uQ - 1 - cgQ / uQ) * (wY : ℚ) + 1) * uQ = (cQ - uQ - cgQ) * (wY : ℚ) + uQ := by
        field_simp [huQ_ne]
      have h3 : ((cQ / uQ - 2 - cgQ / uQ) * (wY : ℚ) + 2) * uQ = (cQ - 2 * uQ - cgQ) * (wY : ℚ) + 2 * uQ := by
        field_simp [huQ_ne]
      have h4 : ((cgQ / uQ - (c.dg : ℚ)) * (wY : ℚ)) * uQ = (cgQ - (c.dg : ℚ) * uQ) * (wY : ℚ) := by
        field_simp [huQ_ne]
      have h5 : ((cQ / uQ - 1 - cgQ / uQ - (dh1 : ℚ)) * (wY : ℚ) + 1) * uQ =
          (cQ - (1 + (dh1 : ℚ)) * uQ - cgQ) * (wY : ℚ) + uQ := by field_simp [huQ_ne]; ring
      have h6 : ((cQ / uQ - 2 - cgQ / uQ - (dh2 : ℚ)) * (wY : ℚ) + 2) * uQ =
          (cQ - (2 + (dh2 : ℚ)) * uQ - cgQ) * (wY : ℚ) + 2 * uQ := by field_simp [huQ_ne]; ring
      have h7 : (((dh2 : ℚ) * (cQ / uQ - 1 - cgQ / uQ) + (dh1 : ℚ) * (cQ / uQ - 2 - cgQ / uQ) -
            (dh1 : ℚ) * (dh2 : ℚ)) * (wY : ℚ) + ((dh2 : ℚ) + 2 * (dh1 : ℚ))) * uQ =
          ((dh2 : ℚ) * (cQ - uQ - cgQ) + (dh1 : ℚ) * (cQ - 2 * uQ - cgQ) - (dh1 : ℚ) * (dh2 : ℚ) * uQ) * (wY : ℚ) +
            ((dh2 : ℚ) + 2 * (dh1 : ℚ)) * uQ := by field_simp [huQ_ne]
      have h8 : (((c.dg : ℚ) * (cQ / uQ - (dStarEff : ℚ)) + (dStarEff : ℚ) * (cgQ / uQ)) * (wY : ℚ)) * uQ =
          ((c.dg : ℚ) * (cQ - (dStarEff : ℚ) * uQ) + (dStarEff : ℚ) * cgQ) * (wY : ℚ) := by field_simp [huQ_ne]
      have h9 : ((cQ / uQ - 4 - cgQ / uQ) * (wY : ℚ) + 1) * uQ = (cQ - 4 * uQ - cgQ) * (wY : ℚ) + uQ := by
        field_simp [huQ_ne]
      have hlinQ : (linZ : ℚ) =
          -(c.ua : ℚ) * (A : ℚ) * uQ +
          (c.vg : ℚ) * (cgQ * (wY : ℚ)) +
          (c.vh1 : ℚ) * ((cQ - uQ - cgQ) * (wY : ℚ) + uQ) +
          (c.vh2 : ℚ) * ((cQ - 2 * uQ - cgQ) * (wY : ℚ) + 2 * uQ) +
          (c.vlcg : ℚ) * ((cgQ - (c.dg : ℚ) * uQ) * (wY : ℚ)) +
          (c.vlch1 : ℚ) * ((cQ - (1 + (dh1 : ℚ)) * uQ - cgQ) * (wY : ℚ) + uQ) +
          (c.vlch2 : ℚ) * ((cQ - (2 + (dh2 : ℚ)) * uQ - cgQ) * (wY : ℚ) + 2 * uQ) +
          (if 1 ≤ dh1 ∧ 2 ≤ dh2 then
            (c.vrh : ℚ) * (((dh2 : ℚ) * (cQ - uQ - cgQ) + (dh1 : ℚ) * (cQ - 2 * uQ - cgQ) -
              (dh1 : ℚ) * (dh2 : ℚ) * uQ) * (wY : ℚ) + ((dh2 : ℚ) + 2 * (dh1 : ℚ)) * uQ) else 0) +
          (if c.hasDStar = true then
            (c.vrf0 : ℚ) * (((c.dg : ℚ) * (cQ - (dStarEff : ℚ) * uQ) + (dStarEff : ℚ) * cgQ) * (wY : ℚ)) else 0) +
          (if c.mode = 2 then (c.vh11 : ℚ) * ((cQ - 4 * uQ - cgQ) * (wY : ℚ) + uQ) else 0) := by
        dsimp only [linZ, cQ, cgQ, uQ]; simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
          Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Int.cast_ite, Int.cast_zero]
      dsimp only [L]
      rw [hlinQ]
      have htop : ∀ x y : ℚ, (x + y) * ((N : ℚ) * (mDen : ℚ) * uQ) =
          x * ((N : ℚ) * (mDen : ℚ) * uQ) + y * ((N : ℚ) * (mDen : ℚ) * uQ) := fun _ _ => add_mul _ _ _
      have htopS : ∀ x y : ℚ, (x - y) * ((N : ℚ) * (mDen : ℚ) * uQ) =
          x * ((N : ℚ) * (mDen : ℚ) * uQ) - y * ((N : ℚ) * (mDen : ℚ) * uQ) := fun _ _ => sub_mul _ _ _
      have htopI : ∀ (P : Prop) [Decidable P] (x : ℚ),
          (if P then x else 0) * ((N : ℚ) * (mDen : ℚ) * uQ) =
          if P then x * ((N : ℚ) * (mDen : ℚ) * uQ) else 0 := fun P _ x => by rw [ite_mul, zero_mul]
      have hrmul : ∀ x y : ℚ, (x + y) * (mDen : ℚ) = x * (mDen : ℚ) + y * (mDen : ℚ) := fun _ _ => add_mul _ _ _
      have hrmulI : ∀ (P : Prop) [Decidable P] (x : ℚ),
          (if P then x else 0) * (mDen : ℚ) = if P then x * (mDen : ℚ) else 0 := fun P _ x => by rw [ite_mul, zero_mul]
      conv_lhs =>
        rw [htop, htop, htop, htop, htop, htop, htop, htop, htop, htopS]
        rw [htopI, htopI, htopI]
        rw [h0, ha, hcl, hcl, hcl, hcl, hcl, hcl, hcl, hcl, hcl]
        rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]
      conv_rhs =>
        rw [hrmul, hrmul, hrmul, hrmul, hrmul, hrmul, hrmul, hrmul, hrmul]
        rw [hrmulI, hrmulI, hrmulI]
      simp only [neg_mul, sub_eq_add_neg, add_assoc]
    constructor
    · intro hm0
      have hm0b : (c.m == 0) = true := beq_iff_eq.mpr hm0
      rw [if_pos hm0b] at hep
      have hZ : c.unNum * (N : ℤ) * uZ + linZ < 0 := by
        have h' := decide_eq_true_eq.mp hep
        simpa [linZ, cZ, cgZ, uZ, dh1, dh2, dStarEff, decide_eq_true_eq, beq_iff_eq] using h'
      have hm1 : (mDen : ℚ) = 1 := by rw [hmDen_eq_orig]; simp [hm0b]
      rw [hL_eq, hm1, mul_one, mul_one]
      have huPos : (0 : ℚ) < (uZ : ℚ) := by rw [huQ]; positivity
      exact div_neg_of_neg_of_pos (by exact_mod_cast hZ) (by positivity)
    · intro hmpos
      have hm0b : (c.m == 0) = false := beq_false_of_ne (Nat.ne_of_gt hmpos)
      rw [if_neg (by simp [hm0b])] at hep
      have hδD : 0 < c.δDen := by by_contra h; simp [Nat.ne_of_gt hmpos, show c.δDen = 0 by omega] at h6
      have hδDQ : (0 : ℚ) < (c.δDen : ℚ) := by exact_mod_cast hδD
      have hZ := decide_eq_true_eq.mp hep
      have hv := vquotNum_div_eq 2 c.m c.s hmpos cNum cDen (by exact_mod_cast hcD)
      simp only [Int.cast_natCast] at hv
      have hmDen_eq : (mDen : ℚ) = (c.m : ℚ) * (c.m : ℚ) := by rw [hmDen_eq_orig]; simp [hm0b]
      have hvD_eq : (vquotDen c.m cDen : ℚ) = (N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (cDen : ℚ) := by
        unfold vquotDen; rw [hmDen_eq]; push_cast; ring
      have huPos : (0 : ℚ) < (uZ : ℚ) := by rw [huQ]; positivity
      have hsub_eq : L ((cNum : ℚ) / (cDen : ℚ)) ((cgNum : ℚ) / (cgDen : ℚ)) -
            (c.vx : ℚ) * vquotLbQ 2 c.m c.s ((cNum : ℚ) / (cDen : ℚ)) =
          (((c.unNum : ℚ) * (N : ℚ) * (uZ : ℚ) + (linZ : ℚ) * (mDen : ℚ)) * (8 * (wY : ℚ) * (cDen : ℚ)) -
            (c.vx : ℚ) * (vquotNum 2 c.m c.s cNum cDen : ℚ) * (cgDen : ℚ)) /
          ((N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (uZ : ℚ)) := by
        rw [hL_eq, ← hv, hvD_eq, huQ]
        field_simp [hNQ.ne', hmDenQ.ne', hcDQ.ne', hcgDQ.ne', hwYQ.ne']
      rw [hsub_eq]
      have hDpos : (0 : ℚ) < (N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (uZ : ℚ) := by positivity
      rw [show -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) = -((c.vx : ℚ) * (c.δNum : ℚ)) / (c.δDen : ℚ) by ring]
      rw [div_lt_div_iff₀ hDpos hδDQ]
      have hZ' : ((c.unNum * (N : ℤ) * uZ + linZ * mDen) * (8 * (wY : ℤ) * (cDen : ℤ)) -
          (c.vx : ℤ) * vquotNum 2 c.m c.s cNum cDen * (cgDen : ℤ)) * (c.δDen : ℤ) <
          -((c.vx : ℤ) * (c.δNum : ℤ) * ((N : ℤ) * mDen * (8 * (wY : ℤ) * (cDen : ℤ)) * uZ)) := by
        rw [hmDen_eq_orig]
        simpa [linZ, cZ, cgZ, uZ, dh1, dh2, dStarEff, hm0b, decide_eq_true_eq, beq_iff_eq] using hZ
      have hQ : (((c.unNum : ℚ) * (N : ℚ) * (uZ : ℚ) + (linZ : ℚ) * (mDen : ℚ)) * (8 * (wY : ℚ) * (cDen : ℚ)) -
          (c.vx : ℚ) * (vquotNum 2 c.m c.s cNum cDen : ℚ) * (cgDen : ℚ)) * (c.δDen : ℚ) <
          -((c.vx : ℚ) * (c.δNum : ℚ) * ((N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (uZ : ℚ))) := by
        exact_mod_cast hZ'
      linarith
  -- Convex combination over the trapezoid `(cVal, cgVal)`!
  -- Notice `cg_max(x) = max(dg, x - capCg + 2/wY)` is CONVEX in `x`, so on `[cLo, cHi]` with `cVal = (1-t)*cLo + t*cHi`:
  -- `cgVal ≤ cg_max(cVal) ≤ (1-t)*cg_max(cLo) + t*cg_max(cHi)`!
  -- Hence `(cVal, cgVal)` lies in the convex hull of the 4 corners `(cLo, dg), (cLo, cg_max(cLo)), (cHi, dg), (cHi, cg_max(cHi))`!
  set capCg : ℕ := max (2 + dh2) (1 + dh1)
  set cLoQ : ℚ := (c.cLoNum : ℚ) / (c.cLoDen : ℚ)
  set cHiQ : ℚ := (c.cHiNum : ℚ) / (c.cHiDen : ℚ)
  set cgMax := fun (x : ℚ) => max (c.dg : ℚ) (x - (capCg : ℚ) + 2 / (wY : ℚ))
  have hcgPair_eq : ∀ (cNum cDen : ℕ) (hcD : 0 < cDen),
      let den := cDen * wY
      let lhs := cNum * wY + 2 * cDen
      let rhs := (c.dg + capCg) * den
      let pr : ℕ × ℕ := if lhs ≤ rhs then (c.dg, 1) else (lhs - capCg * den, den)
      0 < pr.2 ∧ (pr.1 : ℚ) / (pr.2 : ℚ) = cgMax ((cNum : ℚ) / (cDen : ℚ)) := by
    intro cNum cDen hcD
    dsimp only [cgMax]
    have hcDQ : (0 : ℚ) < (cDen : ℚ) := by exact_mod_cast hcD
    have hden_pos : 0 < cDen * wY := Nat.mul_pos hcD (by norm_num [wY, D])
    split_ifs with hle
    · refine ⟨by norm_num, ?_⟩
      rw [Nat.cast_one, div_one]
      symm; apply max_eq_left
      have hQ : (cNum : ℚ) * (wY : ℚ) + 2 * (cDen : ℚ) ≤ ((c.dg : ℚ) + (capCg : ℚ)) * ((cDen : ℚ) * (wY : ℚ)) := by
        exact_mod_cast hle
      have h1 : (cNum : ℚ) / (cDen : ℚ) - (capCg : ℚ) + 2 / (wY : ℚ) =
          ((cNum : ℚ) * (wY : ℚ) + 2 * (cDen : ℚ) - (capCg : ℚ) * ((cDen : ℚ) * (wY : ℚ))) / ((cDen : ℚ) * (wY : ℚ)) := by
        field_simp [hcDQ.ne', hwYQ.ne']; ring
      rw [h1, div_le_iff₀ (by positivity)]; linarith
    · refine ⟨hden_pos, ?_⟩
      have hgt_n : (c.dg + capCg) * (cDen * wY) < cNum * wY + 2 * cDen := Nat.lt_of_not_ge hle
      have hsub : capCg * (cDen * wY) ≤ cNum * wY + 2 * cDen :=
        (Nat.mul_le_mul_right (cDen * wY) (Nat.le_add_left capCg c.dg)).trans hgt_n.le
      have hQ : ((c.dg : ℚ) + (capCg : ℚ)) * ((cDen : ℚ) * (wY : ℚ)) < (cNum : ℚ) * (wY : ℚ) + 2 * (cDen : ℚ) := by
        exact_mod_cast hgt_n
      have h1 : ((cNum * wY + 2 * cDen - capCg * (cDen * wY) : ℕ) : ℚ) / ((cDen * wY : ℕ) : ℚ) =
          (cNum : ℚ) / (cDen : ℚ) - (capCg : ℚ) + 2 / (wY : ℚ) := by
        rw [Nat.cast_sub hsub]; push_cast; field_simp [hcDQ.ne', hwYQ.ne']; ring
      rw [h1]; symm; apply max_eq_right
      have h2 : (cNum : ℚ) / (cDen : ℚ) - (capCg : ℚ) + 2 / (wY : ℚ) =
          ((cNum : ℚ) * (wY : ℚ) + 2 * (cDen : ℚ) - (capCg : ℚ) * ((cDen : ℚ) * (wY : ℚ))) / ((cDen : ℚ) * (wY : ℚ)) := by
        field_simp [hcDQ.ne', hwYQ.ne']; ring
      rw [h2, le_div_iff₀ (by positivity)]; linarith
  have hprLo := hcgPair_eq c.cLoNum c.cLoDen hcLoD
  have hprHi := hcgPair_eq c.cHiNum c.cHiDen hcHiD
  have hC0 := hL_corner c.cLoNum c.cLoDen c.dg 1 hcLoD (by norm_num) hep0
  have hC1 := hL_corner c.cLoNum c.cLoDen _ _ hcLoD hprLo.1 hep1
  have hC2 := hL_corner c.cHiNum c.cHiDen c.dg 1 hcHiD (by norm_num) hep2
  have hC3 := hL_corner c.cHiNum c.cHiDen _ _ hcHiD hprHi.1 hep3
  rw [Nat.cast_one, div_one] at hC0 hC2
  rw [hprLo.2] at hC1
  rw [hprHi.2] at hC3
  -- Express (cVal, cgVal) as convex combination of (cLo, yLo) and (cHi, yHi)!
  set t : ℚ := (cVal - cLoQ) / (cHiQ - cLoQ)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) (sub_pos.mpr hcltQ).le
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hcltQ)).mpr (sub_le_sub_right hhi _)
  have hcVal_eq : cVal = (1 - t) * cLoQ + t * cHiQ := by
    have hden : cHiQ - cLoQ ≠ 0 := (sub_pos.mpr hcltQ).ne'
    dsimp only [t]; field_simp [hden]; ring
  have hcg_ub : cgVal ≤ (1 - t) * cgMax cLoQ + t * cgMax cHiQ := by
    refine hcg_hi.trans ?_
    apply max_le
    · have h1 : (c.dg : ℚ) ≤ cgMax cLoQ := le_max_left _ _
      have h2 : (c.dg : ℚ) ≤ cgMax cHiQ := le_max_left _ _
      have hm1 := mul_le_mul_of_nonneg_left h1 (by linarith only [ht1] : (0 : ℚ) ≤ 1 - t)
      have hm2 := mul_le_mul_of_nonneg_left h2 ht0
      linarith only [hm1, hm2]
    · have h1 : cLoQ - (capCg : ℚ) + 2 / (wY : ℚ) ≤ cgMax cLoQ := le_max_right _ _
      have h2 : cHiQ - (capCg : ℚ) + 2 / (wY : ℚ) ≤ cgMax cHiQ := le_max_right _ _
      have hm1 := mul_le_mul_of_nonneg_left h1 (by linarith only [ht1] : (0 : ℚ) ≤ 1 - t)
      have hm2 := mul_le_mul_of_nonneg_left h2 ht0
      rw [hcVal_eq]; linarith only [hm1, hm2]
  -- L is affine in (x, y)!
  have hL_aff : ∀ x₁ y₁ x₂ y₂ s : ℚ, L ((1 - s) * x₁ + s * x₂) ((1 - s) * y₁ + s * y₂) =
      (1 - s) * L x₁ y₁ + s * L x₂ y₂ := by
    intro x₁ y₁ x₂ y₂ s
    have hconst : ∀ a : ℚ, a = (1 - s) * a + s * a := fun a => by ring
    have hadd : ∀ a₁ a₂ b₁ b₂ : ℚ, ((1 - s) * a₁ + s * a₂) + ((1 - s) * b₁ + s * b₂) =
        (1 - s) * (a₁ + b₁) + s * (a₂ + b₂) := fun _ _ _ _ => by ring
    have haddC : ∀ a₁ a₂ k : ℚ, ((1 - s) * a₁ + s * a₂) + k = (1 - s) * (a₁ + k) + s * (a₂ + k) :=
      fun _ _ _ => by ring
    have hlmul : ∀ k a₁ a₂ : ℚ, k * ((1 - s) * a₁ + s * a₂) = (1 - s) * (k * a₁) + s * (k * a₂) :=
      fun _ _ _ => by ring
    have hrmul : ∀ k a₁ a₂ : ℚ, ((1 - s) * a₁ + s * a₂) * k = (1 - s) * (a₁ * k) + s * (a₂ * k) :=
      fun _ _ _ => by ring
    have hdiv : ∀ k a₁ a₂ : ℚ, ((1 - s) * a₁ + s * a₂) / k = (1 - s) * (a₁ / k) + s * (a₂ / k) :=
      fun _ _ _ => by ring
    have hite : ∀ (P : Prop) [Decidable P] (a₁ a₂ : ℚ),
        (if P then (1 - s) * a₁ + s * a₂ else 0) = (1 - s) * (if P then a₁ else 0) + s * (if P then a₂ else 0) := by
      intro P _ a₁ a₂; split_ifs <;> ring
    have t0 : (c.unNum : ℚ) / (mDen : ℚ) - (c.ua : ℚ) * ((A : ℚ) / (N : ℚ)) =
        (1 - s) * ((c.unNum : ℚ) / (mDen : ℚ) - (c.ua : ℚ) * ((A : ℚ) / (N : ℚ))) +
        s * ((c.unNum : ℚ) / (mDen : ℚ) - (c.ua : ℚ) * ((A : ℚ) / (N : ℚ))) := hconst _
    have t1 : ((1 - s) * y₁ + s * y₂) * (wY : ℚ) / (N : ℚ) =
        (1 - s) * (y₁ * (wY : ℚ) / (N : ℚ)) + s * (y₂ * (wY : ℚ) / (N : ℚ)) := by rw [hrmul, hdiv]
    have t2 : (((1 - s) * x₁ + s * x₂ - 1 - ((1 - s) * y₁ + s * y₂)) * (wY : ℚ) + 1) / (N : ℚ) =
        (1 - s) * (((x₁ - 1 - y₁) * (wY : ℚ) + 1) / (N : ℚ)) + s * (((x₂ - 1 - y₂) * (wY : ℚ) + 1) / (N : ℚ)) := by
      rw [show (1 - s) * x₁ + s * x₂ - 1 - ((1 - s) * y₁ + s * y₂) = (1 - s) * (x₁ - 1 - y₁) + s * (x₂ - 1 - y₂) by ring,
        hrmul, haddC, hdiv]
    have t3 : (((1 - s) * x₁ + s * x₂ - 2 - ((1 - s) * y₁ + s * y₂)) * (wY : ℚ) + 2) / (N : ℚ) =
        (1 - s) * (((x₁ - 2 - y₁) * (wY : ℚ) + 2) / (N : ℚ)) + s * (((x₂ - 2 - y₂) * (wY : ℚ) + 2) / (N : ℚ)) := by
      rw [show (1 - s) * x₁ + s * x₂ - 2 - ((1 - s) * y₁ + s * y₂) = (1 - s) * (x₁ - 2 - y₁) + s * (x₂ - 2 - y₂) by ring,
        hrmul, haddC, hdiv]
    have t4 : (((1 - s) * y₁ + s * y₂ - (c.dg : ℚ)) * (wY : ℚ)) / (N : ℚ) =
        (1 - s) * (((y₁ - (c.dg : ℚ)) * (wY : ℚ)) / (N : ℚ)) + s * (((y₂ - (c.dg : ℚ)) * (wY : ℚ)) / (N : ℚ)) := by
      rw [show (1 - s) * y₁ + s * y₂ - (c.dg : ℚ) = (1 - s) * (y₁ - (c.dg : ℚ)) + s * (y₂ - (c.dg : ℚ)) by ring, hrmul, hdiv]
    have t5 : (((1 - s) * x₁ + s * x₂ - 1 - ((1 - s) * y₁ + s * y₂) - (dh1 : ℚ)) * (wY : ℚ) + 1) / (N : ℚ) =
        (1 - s) * (((x₁ - 1 - y₁ - (dh1 : ℚ)) * (wY : ℚ) + 1) / (N : ℚ)) +
        s * (((x₂ - 1 - y₂ - (dh1 : ℚ)) * (wY : ℚ) + 1) / (N : ℚ)) := by
      rw [show (1 - s) * x₁ + s * x₂ - 1 - ((1 - s) * y₁ + s * y₂) - (dh1 : ℚ) =
          (1 - s) * (x₁ - 1 - y₁ - (dh1 : ℚ)) + s * (x₂ - 1 - y₂ - (dh1 : ℚ)) by ring, hrmul, haddC, hdiv]
    have t6 : (((1 - s) * x₁ + s * x₂ - 2 - ((1 - s) * y₁ + s * y₂) - (dh2 : ℚ)) * (wY : ℚ) + 2) / (N : ℚ) =
        (1 - s) * (((x₁ - 2 - y₁ - (dh2 : ℚ)) * (wY : ℚ) + 2) / (N : ℚ)) +
        s * (((x₂ - 2 - y₂ - (dh2 : ℚ)) * (wY : ℚ) + 2) / (N : ℚ)) := by
      rw [show (1 - s) * x₁ + s * x₂ - 2 - ((1 - s) * y₁ + s * y₂) - (dh2 : ℚ) =
          (1 - s) * (x₁ - 2 - y₁ - (dh2 : ℚ)) + s * (x₂ - 2 - y₂ - (dh2 : ℚ)) by ring, hrmul, haddC, hdiv]
    have t7 : ((((dh2 : ℚ) * ((1 - s) * x₁ + s * x₂ - 1 - ((1 - s) * y₁ + s * y₂)) +
          (dh1 : ℚ) * ((1 - s) * x₁ + s * x₂ - 2 - ((1 - s) * y₁ + s * y₂)) - (dh1 : ℚ) * (dh2 : ℚ)) * (wY : ℚ) +
          ((dh2 : ℚ) + 2 * (dh1 : ℚ))) / (N : ℚ)) =
        (1 - s) * ((((dh2 : ℚ) * (x₁ - 1 - y₁) + (dh1 : ℚ) * (x₁ - 2 - y₁) - (dh1 : ℚ) * (dh2 : ℚ)) * (wY : ℚ) +
          ((dh2 : ℚ) + 2 * (dh1 : ℚ))) / (N : ℚ)) +
        s * ((((dh2 : ℚ) * (x₂ - 1 - y₂) + (dh1 : ℚ) * (x₂ - 2 - y₂) - (dh1 : ℚ) * (dh2 : ℚ)) * (wY : ℚ) +
          ((dh2 : ℚ) + 2 * (dh1 : ℚ))) / (N : ℚ)) := by
      rw [show (dh2 : ℚ) * ((1 - s) * x₁ + s * x₂ - 1 - ((1 - s) * y₁ + s * y₂)) +
            (dh1 : ℚ) * ((1 - s) * x₁ + s * x₂ - 2 - ((1 - s) * y₁ + s * y₂)) - (dh1 : ℚ) * (dh2 : ℚ) =
          (1 - s) * ((dh2 : ℚ) * (x₁ - 1 - y₁) + (dh1 : ℚ) * (x₁ - 2 - y₁) - (dh1 : ℚ) * (dh2 : ℚ)) +
          s * ((dh2 : ℚ) * (x₂ - 1 - y₂) + (dh1 : ℚ) * (x₂ - 2 - y₂) - (dh1 : ℚ) * (dh2 : ℚ)) by ring,
        hrmul, haddC, hdiv]
    have t8 : ((((c.dg : ℚ) * ((1 - s) * x₁ + s * x₂ - (dStarEff : ℚ)) +
          (dStarEff : ℚ) * ((1 - s) * y₁ + s * y₂)) * (wY : ℚ)) / (N : ℚ)) =
        (1 - s) * ((((c.dg : ℚ) * (x₁ - (dStarEff : ℚ)) + (dStarEff : ℚ) * y₁) * (wY : ℚ)) / (N : ℚ)) +
        s * ((((c.dg : ℚ) * (x₂ - (dStarEff : ℚ)) + (dStarEff : ℚ) * y₂) * (wY : ℚ)) / (N : ℚ)) := by
      rw [show (c.dg : ℚ) * ((1 - s) * x₁ + s * x₂ - (dStarEff : ℚ)) + (dStarEff : ℚ) * ((1 - s) * y₁ + s * y₂) =
          (1 - s) * ((c.dg : ℚ) * (x₁ - (dStarEff : ℚ)) + (dStarEff : ℚ) * y₁) +
          s * ((c.dg : ℚ) * (x₂ - (dStarEff : ℚ)) + (dStarEff : ℚ) * y₂) by ring, hrmul, hdiv]
    have t9 : (((1 - s) * x₁ + s * x₂ - 4 - ((1 - s) * y₁ + s * y₂)) * (wY : ℚ) + 1) / (N : ℚ) =
        (1 - s) * (((x₁ - 4 - y₁) * (wY : ℚ) + 1) / (N : ℚ)) + s * (((x₂ - 4 - y₂) * (wY : ℚ) + 1) / (N : ℚ)) := by
      rw [show (1 - s) * x₁ + s * x₂ - 4 - ((1 - s) * y₁ + s * y₂) = (1 - s) * (x₁ - 4 - y₁) + s * (x₂ - 4 - y₂) by ring,
        hrmul, haddC, hdiv]
    dsimp only [L]
    conv_lhs =>
      rw [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9]
      rw [hlmul, hlmul, hlmul, hlmul, hlmul, hlmul, hlmul, hlmul, hlmul]
      rw [hite, hite, hite]
      rw [hadd, hadd, hadd, hadd, hadd, hadd, hadd, hadd, hadd]
  have hL_y_bound : ∀ B : ℚ,
      L cLoQ (c.dg : ℚ) < B → L cLoQ (cgMax cLoQ) < B →
      L cHiQ (c.dg : ℚ) < B → L cHiQ (cgMax cHiQ) < B →
      L cVal cgVal < B := by
    intro B hb0 hb1 hb2 hb3
    have hL_top : L cVal ((1 - t) * cgMax cLoQ + t * cgMax cHiQ) < B := by
      rw [hcVal_eq, hL_aff]; exact convex_comb_lt ht0 ht1 hb1 hb3
    have hL_bot : L cVal (c.dg : ℚ) < B := by
      have : (c.dg : ℚ) = (1 - t) * (c.dg : ℚ) + t * (c.dg : ℚ) := by ring
      rw [hcVal_eq, this, hL_aff]; exact convex_comb_lt ht0 ht1 hb0 hb2
    set yTop : ℚ := (1 - t) * cgMax cLoQ + t * cgMax cHiQ
    by_cases heq : (c.dg : ℚ) = yTop
    · have hcg_eq : cgVal = (c.dg : ℚ) := by linarith
      rwa [hcg_eq]
    · have hlt : (c.dg : ℚ) < yTop := lt_of_le_of_ne (hcg_lo.trans hcg_ub) heq
      set u : ℚ := (cgVal - (c.dg : ℚ)) / (yTop - (c.dg : ℚ))
      have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hcg_lo) (sub_pos.mpr hlt).le
      have hu1 : u ≤ 1 := (div_le_one (sub_pos.mpr hlt)).mpr (sub_le_sub_right hcg_ub _)
      have hy_eq : cgVal = (1 - u) * (c.dg : ℚ) + u * yTop := by
        have hden : yTop - (c.dg : ℚ) ≠ 0 := (sub_pos.mpr hlt).ne'
        dsimp only [u]; field_simp [hden]; ring
      have hx_eq : cVal = (1 - u) * cVal + u * cVal := by ring
      rw [hx_eq, hy_eq, hL_aff]; exact convex_comb_lt hu0 hu1 hL_bot hL_top
  constructor
  · intro hm0
    have hvx0 : c.vx = 0 := by by_contra hne; simp [hm0, hne] at h5
    have hL_lt : L cVal cgVal < 0 := hL_y_bound 0 (hC0.1 hm0) (hC1.1 hm0) (hC2.1 hm0) (hC3.1 hm0)
    have h0le : (0 : ℚ) ≤ L cVal cgVal := by simpa [hvx0] using hsum_all
    linarith
  · intro hmpos
    have hm0b : (c.m == 0) = false := beq_false_of_ne (Nat.ne_of_gt hmpos)
    have hvxpos : 0 < c.vx := by by_contra h; simp [Nat.ne_of_gt hmpos, show c.vx = 0 by omega] at h6
    have hvxQ : (0 : ℚ) < (c.vx : ℚ) := by exact_mod_cast hvxpos
    have hsec := vquotLbQ_ge_secant 2 c.m c.s hmpos hlo hhi hcltQ
    -- Subtract the secant linear function `S(x) = vx * ((1 - (x-cLo)/(cHi-cLo))*vqLo + ((x-cLo)/(cHi-cLo))*vqHi)`!
    set vLo : ℚ := vquotLbQ 2 c.m c.s cLoQ
    set vHi : ℚ := vquotLbQ 2 c.m c.s cHiQ
    set B : ℚ := -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ))
    have hL_top : L cVal ((1 - t) * cgMax cLoQ + t * cgMax cHiQ) - (c.vx : ℚ) * ((1 - t) * vLo + t * vHi) < B := by
      rw [hcVal_eq, hL_aff]
      have hcc := convex_comb_lt ht0 ht1 (hC1.2 hmpos) (hC3.2 hmpos)
      linarith
    have hL_bot : L cVal (c.dg : ℚ) - (c.vx : ℚ) * ((1 - t) * vLo + t * vHi) < B := by
      have : (c.dg : ℚ) = (1 - t) * (c.dg : ℚ) + t * (c.dg : ℚ) := by ring
      rw [hcVal_eq, this, hL_aff]
      have hcc := convex_comb_lt ht0 ht1 (hC0.2 hmpos) (hC2.2 hmpos)
      linarith
    have hL_lt : L cVal cgVal - (c.vx : ℚ) * ((1 - t) * vLo + t * vHi) < B := by
      set yTop : ℚ := (1 - t) * cgMax cLoQ + t * cgMax cHiQ
      by_cases heq : (c.dg : ℚ) = yTop
      · have hcg_eq : cgVal = (c.dg : ℚ) := by linarith
        rwa [hcg_eq]
      · have hlt : (c.dg : ℚ) < yTop := lt_of_le_of_ne (hcg_lo.trans hcg_ub) heq
        set u : ℚ := (cgVal - (c.dg : ℚ)) / (yTop - (c.dg : ℚ))
        have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hcg_lo) (sub_pos.mpr hlt).le
        have hu1 : u ≤ 1 := (div_le_one (sub_pos.mpr hlt)).mpr (sub_le_sub_right hcg_ub _)
        have hy_eq : cgVal = (1 - u) * (c.dg : ℚ) + u * yTop := by
          have hden : yTop - (c.dg : ℚ) ≠ 0 := (sub_pos.mpr hlt).ne'
          dsimp only [u]; field_simp [hden]; ring
        have hx_eq : cVal = (1 - u) * cVal + u * cVal := by ring
        rw [hx_eq, hy_eq, hL_aff]
        have hcc := convex_comb_lt hu0 hu1 hL_bot hL_top
        linarith
    rw [if_neg (by simp [hm0b])] at hcap
    refine ⟨?_, hcap⟩
    have h1 : (c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) <
        (c.vx : ℚ) * (vquotLbQ 2 c.m c.s cVal - (∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) / (N : ℚ)) := by
      dsimp only [B, vLo, vHi] at hL_lt
      have hsm := mul_le_mul_of_nonneg_left hsec hvxQ.le
      linarith only [hL_lt, hsum_all, hsm]
    exact lt_of_mul_lt_mul_left h1 hvxQ.le

/-! ### Part 5: Table 3 Subcase 2B (`(8, 6, 10, 11)`) pure-`Int` checker & soundness -/

def t3_2BVrf0Sub (dSub k rSub : ℕ) : ℕ :=
  if k == 0 then 0
  else
    let vk := resOrdWeighted2Fast 11 (4 * k + 4) (dSub / 2) rSub - 2 * dSub
    let vp0 := resOrdExact 0 (2 * k - 2) dSub rSub + 11 * (rSub - dSub)
    let vp := ((List.range 12).map (fun d0 =>
      resOrdExact d0 (2 * k - 2) dSub rSub + (11 - d0) * (rSub - dSub))).foldl Nat.min vp0
    max vk vp

lemma t3_2BVrf0Sub_eq_large (dSub k rSub : ℕ) (hd : dSub = 2 ∨ dSub = 4) (hk : 14 ≤ k) :
    t3_2BVrf0Sub dSub k rSub = 2 * dSub * k + 11 * rSub - 11 * dSub := by
  have hk0 : (k == 0) = false := by simp; omega
  have hvp_le : ((List.range 12).map (fun d0 =>
      resOrdExact d0 (2 * k - 2) dSub rSub + (11 - d0) * (rSub - dSub))).foldl Nat.min
        (resOrdExact 0 (2 * k - 2) dSub rSub + 11 * (rSub - dSub)) ≤
      2 * dSub * k + 11 * rSub - 11 * dSub := by
    have hfold_le_mem : ∀ (l : List ℕ) (init x : ℕ), x ∈ l → l.foldl Nat.min init ≤ x := by
      intro l; induction l with
      | nil => intro _ _ hx; cases hx
      | cons a t ih =>
        intro init x hx; simp only [List.foldl_cons, List.mem_cons] at hx ⊢
        rcases hx with rfl | ht
        · have hle : ∀ (l' : List ℕ) (z : ℕ), l'.foldl Nat.min z ≤ z := by
            intro l'; induction l' with
            | nil => intro _; exact le_rfl
            | cons b bs ih' => intro z; simp only [List.foldl_cons]; exact (ih' _).trans (Nat.min_le_left _ _)
          exact (hle t _).trans (Nat.min_le_right _ _)
        · exact ih _ x ht
    have hmem : resOrdExact 11 (2 * k - 2) dSub rSub + (11 - 11) * (rSub - dSub) ∈
        (List.range 12).map (fun d0 => resOrdExact d0 (2 * k - 2) dSub rSub + (11 - d0) * (rSub - dSub)) :=
      List.mem_map.mpr ⟨11, List.mem_range.mpr (by omega), rfl⟩
    refine (hfold_le_mem _ _ _ hmem).trans ?_
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    unfold resOrdExact
    have h0 : 11 - (2 * k - 2) = 0 := by omega
    rcases hd with rfl | rfl <;> (simp only [OfNat.ofNat_ne_zero, ↓reduceIte, h0, Nat.zero_mul, Nat.add_zero]; omega)
  unfold t3_2BVrf0Sub
  simp only [hk0, Bool.false_eq_true, ↓reduceIte, resOrdWeighted2Fast_eq]
  have hvk : resOrdWeighted 11 (4 * k + 4) (dSub / 2) rSub 2 - 2 * dSub =
      2 * dSub * k + 11 * rSub - 11 * dSub := by
    rw [resOrdWeighted_eq_of_two_mul_le 11 (4 * k + 4) (dSub / 2) rSub (by omega)
      (by rcases hd with rfl | rfl <;> omega) (by omega)]
    rcases hd with rfl | rfl <;> omega
  rw [hvk]; exact Nat.max_eq_left hvp_le

/-- Table 3 Subcase 2B certificate for `(8, 6, 10, 11)`. -/
structure T3_2BCert where
  cLoNum : ℕ
  cLoDen : ℕ
  cHiNum : ℕ
  cHiDen : ℕ
  m : ℕ
  s : ℕ
  ua : ℕ
  vq : ℕ
  vg1 : ℕ
  vh1 : ℕ
  vu : ℕ
  vlcq : ℕ
  vlcg1 : ℕ
  vlch1 : ℕ
  vrq : ℕ
  vx : ℕ
  vrf0q : ℕ
  vrf0g1 : ℕ
  unNum : ℤ
  δNum : ℕ
  δDen : ℕ
  cap : CapWitness
  deriving Repr

/-- Check one 2B corner `(c, cg, cq) = (cNum/cDen, cgNum/cgDen, cqNum/cqDen)` in pure `Int`! -/
def checkT3_2BCorner (c : T3_2BCert) (cNum cDen cgNum cgDen cqNum cqDen : ℕ) : Bool :=
  let mDen : ℤ := if c.m == 0 then 1 else (c.m : ℤ) * (c.m : ℤ)
  let uZ : ℤ := (cDen : ℤ) * (cgDen : ℤ) * (cqDen : ℤ)
  let cZ : ℤ := (cNum : ℤ) * (cgDen : ℤ) * (cqDen : ℤ)
  let cgZ : ℤ := (cgNum : ℤ) * (cDen : ℤ) * (cqDen : ℤ)
  let cqZ : ℤ := (cqNum : ℤ) * (cDen : ℤ) * (cgDen : ℤ)
  let linNum : ℤ :=
    -(c.ua : ℤ) * (A : ℤ) * uZ +
    (c.vq : ℤ) * (cqZ * (wY : ℤ)) +
    (c.vg1 : ℤ) * ((cgZ - cqZ) * (wY : ℤ)) +
    (c.vh1 : ℤ) * ((cZ - uZ - cgZ) * (wY : ℤ) + uZ) +
    (c.vu : ℤ) * ((cZ - 2 * uZ - cgZ - cqZ) * (wY : ℤ) + 2 * uZ) +
    (c.vlcq : ℤ) * ((cqZ - 2 * uZ) * (wY : ℤ)) +
    (c.vlcg1 : ℤ) * ((cgZ - cqZ - 4 * uZ) * (wY : ℤ)) +
    (c.vlch1 : ℤ) * ((cZ - 5 * uZ - cgZ) * (wY : ℤ) + uZ) +
    (c.vrq : ℤ) * ((2 * (cZ - uZ - cgZ) + 4 * cqZ - 8 * uZ) * (wY : ℤ) + 2 * uZ) +
    (c.vrf0q : ℤ) * ((2 * (cZ - 11 * uZ) + 11 * cqZ) * (wY : ℤ)) +
    (c.vrf0g1 : ℤ) * ((4 * (cZ - 11 * uZ) + 11 * (cgZ - cqZ)) * (wY : ℤ))
  if c.m == 0 then
    c.unNum * (N : ℤ) * uZ + linNum < 0
  else
    let vN : ℤ := vquotNum 2 c.m c.s (cNum : ℤ) (cDen : ℤ)
    let scale : ℤ := 8 * (wY : ℤ) * (cDen : ℤ)
    let objNum : ℤ := (c.unNum * (N : ℤ) * uZ + linNum * mDen) * scale -
      (c.vx : ℤ) * vN * ((cgDen : ℤ) * (cqDen : ℤ))
    let D : ℤ := (N : ℤ) * mDen * scale * uZ
    objNum * (c.δDen : ℤ) < -((c.vx : ℤ) * (c.δNum : ℤ) * D)

def checkT3_2BTri (c : T3_2BCert) (cNum cDen : ℕ) : Bool :=
  let dW := cDen * wY
  let cPlus2 := cNum * wY + 2 * cDen
  decide (11 * dW ≤ cPlus2 ∧ cPlus2 ≤ 12 * dW) &&
  checkT3_2BCorner c cNum cDen 6 1 2 1 &&
  checkT3_2BCorner c cNum cDen (cPlus2 - 5 * dW) dW 2 1 &&
  checkT3_2BCorner c cNum cDen (cPlus2 - 5 * dW) dW (cPlus2 - 9 * dW) dW

def checkT3_2BCert (c : T3_2BCert) : Bool :=
  if c.cLoDen == 0 || c.cHiDen == 0 then false
  else if !decide ((c.cLoNum : ℤ) * (c.cHiDen : ℤ) < (c.cHiNum : ℤ) * (c.cLoDen : ℤ)) then false
  else if c.m == 0 && c.vx != 0 then false
  else if c.m != 0 && (c.s < 2 || c.vx == 0 || c.δNum == 0 || c.δDen == 0) then false
  else if decide (c.unNum < 0) then false
  else
    let K0 : ℕ := 14
    let mDenNat : ℕ := if c.m == 0 then 1 else c.m * c.m
    let mDen : ℤ := (mDenNat : ℤ)
    let unNat : ℕ := c.unNum.toNat
    let slopeNum : ℤ := rankDiffNum 2 c.m c.s K0 - rankDiffNum 2 c.m c.s (K0 - 1)
    let sA : Bool := (c.vx : ℤ) * slopeNum ≤
      (2 * (c.vu : ℤ) + 2 * (c.vlch1 : ℤ) + 4 * (c.vrq : ℤ) + 4 * (c.vrf0q : ℤ) + 8 * (c.vrf0g1 : ℤ)) * mDen
    let sB : Bool := (c.vx : ℤ) * slopeNum ≤
      (2 * (c.vlcg1 : ℤ) + 4 * (c.vrf0q : ℤ) + 30 * (c.vrf0g1 : ℤ)) * mDen
    let sC : Bool := (c.vx : ℤ) * slopeNum ≤
      (2 * (c.vlcq : ℤ) + 8 * (c.vrq : ℤ) + 26 * (c.vrf0q : ℤ) + 8 * (c.vrf0g1 : ℤ)) * mDen
    let sD : Bool := (c.vx : ℤ) * slopeNum ≤
      ((c.vlcq : ℤ) + (c.vlch1 : ℤ) + 6 * (c.vrq : ℤ) + 15 * (c.vrf0q : ℤ) + 8 * (c.vrf0g1 : ℤ)) * mDen
    let ptOk : Bool :=
      allNat (K0 + 1) fun k =>
        let rkN : ℕ := rkDiffNat 2 c.m c.s k
        if Nat.ble (c.vx * rkN + c.ua * mDenNat) unNat then true
        else
          allNat (2 * k + 1) fun rr =>
            allNat (rr + 1) fun rq =>
              let h1 : ℕ := c.ua - (c.vq * rq + c.vg1 * (rr - rq) + c.vh1 * (2 * k - 1 - rr))
              let baseSub : ℕ :=
                c.vu * (2 * k - 2 - rr - rq) +
                c.vlcq * (rq - 2) +
                c.vlcg1 * (rr - rq - 4) +
                c.vlch1 * (2 * k - 1 - rr - 4) +
                c.vrq * resOrdExact 4 (2 * k - 1 - rr) 2 rq
              if Nat.ble (c.vx * rkN + h1 * mDenNat) (unNat + baseSub * mDenNat) then true
              else
                let rf0q : ℕ := if k == 14 then 4 * k + 11 * rq - 22 else t3_2BVrf0Sub 2 k rq
                let rf0g1 : ℕ := if k == 14 then 8 * k + 11 * (rr - rq) - 44 else t3_2BVrf0Sub 4 k (rr - rq)
                Nat.ble (c.vx * rkN + h1 * mDenNat)
                  (unNat + (baseSub + c.vrf0q * rf0q + c.vrf0g1 * rf0g1) * mDenNat)
    let epOk : Bool := checkT3_2BTri c c.cLoNum c.cLoDen && checkT3_2BTri c c.cHiNum c.cHiDen
    let capOk : Bool :=
      if c.m == 0 then true
      else checkCapWitness 2 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 1 c.cap
    sA && sB && sC && sD && ptOk && epOk && capOk

/-- Soundness of `checkT3_2BCert` for `(8, 6, 10, 11)` Subcase 2B (`h2 = u(X)*q, g = q*g1, deg_Y q = 2, deg_Y g1 = 4`)! -/
theorem checkT3_2BCert_sound (c : T3_2BCert) (hchk : checkT3_2BCert c = true)
    (cVal cgVal cqVal : ℚ)
    (hlo : (c.cLoNum : ℚ) / (c.cLoDen : ℚ) ≤ cVal)
    (hhi : cVal ≤ (c.cHiNum : ℚ) / (c.cHiDen : ℚ))
    (hcq_lo : (2 : ℚ) ≤ cqVal)
    (hcg_lo : cqVal + 4 ≤ cgVal)
    (hcg_hi1 : cgVal ≤ cVal - 5 + 2 / (wY : ℚ))
    (Az : Finset Idx) (hAz : A ≤ Az.card)
    (k rr rq : Idx → ℕ) (hrr_le : ∀ i, rr i ≤ 2 * k i) (hrq_le : ∀ i, rq i ≤ rr i)
    (hq : (∑ i ∈ Az, (rq i : ℚ)) ≤ cqVal * (wY : ℚ))
    (hg1 : (∑ i ∈ Az, ((rr i - rq i : ℕ) : ℚ)) ≤ (cgVal - cqVal) * (wY : ℚ))
    (hh1 : (∑ i ∈ Az, ((2 * k i - 1 - rr i : ℕ) : ℚ)) ≤ (cVal - 1 - cgVal) * (wY : ℚ) + 1)
    (hu : (∑ i : Idx, ((2 * k i - 2 - rr i - rq i : ℕ) : ℚ)) ≤ (cVal - 2 - cgVal - cqVal) * (wY : ℚ) + 2)
    (hlcq : (∑ i : Idx, ((rq i - 2 : ℕ) : ℚ)) ≤ (cqVal - 2) * (wY : ℚ))
    (hlcg1 : (∑ i : Idx, ((rr i - rq i - 4 : ℕ) : ℚ)) ≤ (cgVal - cqVal - 4) * (wY : ℚ))
    (hlch1 : (∑ i : Idx, ((2 * k i - 1 - rr i - 4 : ℕ) : ℚ)) ≤ (cVal - 5 - cgVal) * (wY : ℚ) + 1)
    (hrq_res : (∑ i : Idx, (resOrdExact 4 (2 * k i - 1 - rr i) 2 (rq i) : ℚ)) ≤
      (2 * (cVal - 1 - cgVal) + 4 * cqVal - 8) * (wY : ℚ) + 2)
    (hrf0q : (∑ i : Idx, (t3_2BVrf0Sub 2 (k i) (rq i) : ℚ)) ≤ (2 * (cVal - 11) + 11 * cqVal) * (wY : ℚ))
    (hrf0g1 : (∑ i : Idx, (t3_2BVrf0Sub 4 (k i) (rr i - rq i) : ℚ)) ≤
      (4 * (cVal - 11) + 11 * (cgVal - cqVal)) * (wY : ℚ)) :
    (c.m = 0 → False) ∧
    (0 < c.m →
      (c.δNum : ℚ) / (c.δDen : ℚ) <
        vquotLbQ 2 c.m c.s cVal - (∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) / (N : ℚ) ∧
      checkCapWitness 2 c.m c.s c.cHiNum c.cHiDen c.δNum c.δDen 1 1 1 c.cap = true) := by
  unfold checkT3_2BCert at hchk; dsimp only at hchk
  by_cases h1 : (c.cLoDen == 0 || c.cHiDen == 0) = true
  · rw [if_pos h1] at hchk; cases hchk
  rw [if_neg h1] at hchk
  by_cases h2 : (!decide ((c.cLoNum : ℤ) * (c.cHiDen : ℤ) < (c.cHiNum : ℤ) * (c.cLoDen : ℤ))) = true
  · rw [if_pos h2] at hchk; cases hchk
  rw [if_neg h2] at hchk
  by_cases h3 : (c.m == 0 && c.vx != 0) = true
  · rw [if_pos h3] at hchk; cases hchk
  rw [if_neg h3] at hchk
  by_cases h4 : (c.m != 0 && (c.s < 2 || c.vx == 0 || c.δNum == 0 || c.δDen == 0)) = true
  · rw [if_pos h4] at hchk; cases hchk
  rw [if_neg h4] at hchk
  by_cases h5 : decide (c.unNum < 0) = true
  · rw [if_pos h5] at hchk; cases hchk
  rw [if_neg h5] at hchk
  have hun_nn : 0 ≤ c.unNum := by
    by_contra hlt; push Not at hlt; exact h5 (decide_eq_true hlt)
  have hun_toNat : (c.unNum.toNat : ℤ) = c.unNum := Int.toNat_of_nonneg hun_nn
  have hcLoD : 0 < c.cLoDen := by by_contra h; simp [show c.cLoDen = 0 by omega] at h1
  have hcHiD : 0 < c.cHiDen := by by_contra h; simp [show c.cHiDen = 0 by omega] at h1
  have hcltZ : (c.cLoNum : ℤ) * c.cHiDen < (c.cHiNum : ℤ) * c.cLoDen := by
    have h' : decide ((c.cLoNum : ℤ) * c.cHiDen < (c.cHiNum : ℤ) * c.cLoDen) = true := by
      cases hb : decide ((c.cLoNum : ℤ) * c.cHiDen < (c.cHiNum : ℤ) * c.cLoDen)
      · simp [hb] at h2
      · rfl
    exact decide_eq_true_eq.mp h'
  have hcLoDQ : (0 : ℚ) < (c.cLoDen : ℚ) := by exact_mod_cast hcLoD
  have hcHiDQ : (0 : ℚ) < (c.cHiDen : ℚ) := by exact_mod_cast hcHiD
  have hcltQ : (c.cLoNum : ℚ) / (c.cLoDen : ℚ) < (c.cHiNum : ℚ) / (c.cHiDen : ℚ) := by
    rw [div_lt_div_iff₀ hcLoDQ hcHiDQ]; exact_mod_cast hcltZ
  set mDenNat : ℕ := if c.m == 0 then 1 else c.m * c.m
  set mDen : ℤ := (mDenNat : ℤ)
  have hmDen_eq_orig : mDen = if c.m == 0 then 1 else (c.m : ℤ) * (c.m : ℤ) := by
    dsimp [mDen, mDenNat]; split_ifs <;> simp
  have hmDen_pos : 0 < mDen := by
    rw [hmDen_eq_orig]; split_ifs with hm0
    · norm_num
    · have : 0 < c.m := Nat.pos_of_ne_zero (fun h => by simp [h] at hm0); positivity
  have hmDenQ : (0 : ℚ) < (mDen : ℚ) := by exact_mod_cast hmDen_pos
  have hNQ : (0 : ℚ) < (N : ℚ) := by norm_num [N]
  have hwYQ : (0 : ℚ) < (wY : ℚ) := by norm_num [wY, D]
  have hcardIdx : (Fintype.card Idx : ℚ) = (N : ℚ) := by
    have : Fintype.card Idx = N := by simp [Idx, N]
    exact_mod_cast this
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨hsA, hsB⟩, hsC⟩, hsD⟩, hpt⟩, ⟨hepLo, hepHi⟩⟩, hcap⟩
  have hrk_eq : ∀ k0 : ℕ, (c.vx : ℚ) * ((rankDiffNum 2 c.m c.s k0 : ℚ) / (mDen : ℚ)) =
      (c.vx : ℚ) * rankDiffQ 2 c.m c.s k0 := by
    intro k0
    by_cases hm0 : c.m = 0
    · have hvx0 : c.vx = 0 := by by_contra hne; simp [hm0, hne] at h3
      simp [hvx0]
    · have hmpos : 0 < c.m := Nat.pos_of_ne_zero hm0
      have hmne : (c.m == 0) = false := beq_false_of_ne hm0
      have hmDen_eq : (mDen : ℚ) = (c.m : ℚ) * (c.m : ℚ) := by rw [hmDen_eq_orig]; simp [hmne]
      rw [hmDen_eq, rankDiffNum_div_eq 2 c.m c.s k0 hmpos]
  have hpt_le : ∀ (k0 : ℕ), k0 ≤ 14 → ∀ (rr0 : ℕ), rr0 ≤ 2 * k0 → ∀ (rq0 : ℕ), rq0 ≤ rr0 →
      (c.vx : ℚ) * rankDiffQ 2 c.m c.s k0 +
      max (0 : ℚ) ((c.ua : ℚ) - (c.vq : ℚ) * (rq0 : ℚ) - (c.vg1 : ℚ) * ((rr0 - rq0 : ℕ) : ℚ) -
        (c.vh1 : ℚ) * ((2 * k0 - 1 - rr0 : ℕ) : ℚ)) ≤
      (c.unNum : ℚ) / (mDen : ℚ) +
      (c.vu : ℚ) * ((2 * k0 - 2 - rr0 - rq0 : ℕ) : ℚ) +
      (c.vlcq : ℚ) * ((rq0 - 2 : ℕ) : ℚ) +
      (c.vlcg1 : ℚ) * ((rr0 - rq0 - 4 : ℕ) : ℚ) +
      (c.vlch1 : ℚ) * ((2 * k0 - 1 - rr0 - 4 : ℕ) : ℚ) +
      (c.vrq : ℚ) * (resOrdExact 4 (2 * k0 - 1 - rr0) 2 rq0 : ℚ) +
      (c.vrf0q : ℚ) * (t3_2BVrf0Sub 2 k0 rq0 : ℚ) +
      (c.vrf0g1 : ℚ) * (t3_2BVrf0Sub 4 k0 (rr0 - rq0) : ℚ) := by
    intro k0 hk0 rr0 hrr0 rq0 hrq0
    set rkN : ℕ := rkDiffNat 2 c.m c.s k0
    set h1 : ℕ := c.ua - (c.vq * rq0 + c.vg1 * (rr0 - rq0) + c.vh1 * (2 * k0 - 1 - rr0))
    set baseSub : ℕ :=
      c.vu * (2 * k0 - 2 - rr0 - rq0) +
      c.vlcq * (rq0 - 2) +
      c.vlcg1 * (rr0 - rq0 - 4) +
      c.vlch1 * (2 * k0 - 1 - rr0 - 4) +
      c.vrq * resOrdExact 4 (2 * k0 - 1 - rr0) 2 rq0
    set subTot : ℕ :=
      baseSub + c.vrf0q * t3_2BVrf0Sub 2 k0 rq0 + c.vrf0g1 * t3_2BVrf0Sub 4 k0 (rr0 - rq0)
    have hNat : c.vx * rkN + h1 * mDenNat ≤ c.unNum.toNat + subTot * mDenNat := by
      have hk_ok := (allNat_eq_true_iff _ _).mp hpt k0 (by omega)
      by_cases hU : Nat.ble (c.vx * rkN + c.ua * mDenNat) c.unNum.toNat = true
      · have hleU := Nat.ble_eq.mp hU
        have hh1_le : h1 ≤ c.ua := Nat.sub_le _ _
        have hm := Nat.mul_le_mul_right mDenNat hh1_le
        omega
      · rw [if_neg hU] at hk_ok
        have hrr_ok := (allNat_eq_true_iff _ _).mp hk_ok rr0 (by omega)
        have hrq_ok := (allNat_eq_true_iff _ _).mp hrr_ok rq0 (by omega)
        by_cases hB : Nat.ble (c.vx * rkN + h1 * mDenNat) (c.unNum.toNat + baseSub * mDenNat) = true
        · have hleB := Nat.ble_eq.mp hB
          have hsub_le : baseSub ≤ subTot := by dsimp only [subTot]; omega
          have hm := Nat.mul_le_mul_right mDenNat hsub_le
          omega
        · rw [if_neg hB] at hrq_ok
          have hq_eq : (if k0 == 14 then 4 * k0 + 11 * rq0 - 22 else t3_2BVrf0Sub 2 k0 rq0) =
              t3_2BVrf0Sub 2 k0 rq0 := by
            by_cases hk14 : k0 = 14
            · subst hk14; simp only [beq_self_eq_true, ↓reduceIte]
              simpa using (t3_2BVrf0Sub_eq_large 2 14 rq0 (Or.inl rfl) le_rfl).symm
            · simp [beq_false_of_ne hk14]
          have hg1_eq : (if k0 == 14 then 8 * k0 + 11 * (rr0 - rq0) - 44 else t3_2BVrf0Sub 4 k0 (rr0 - rq0)) =
              t3_2BVrf0Sub 4 k0 (rr0 - rq0) := by
            by_cases hk14 : k0 = 14
            · subst hk14; simp only [beq_self_eq_true, ↓reduceIte]
              simpa using (t3_2BVrf0Sub_eq_large 4 14 (rr0 - rq0) (Or.inr rfl) le_rfl).symm
            · simp [beq_false_of_ne hk14]
          rw [hq_eq, hg1_eq] at hrq_ok
          exact Nat.ble_eq.mp hrq_ok
    have hZ : ((c.vx : ℤ) * rankDiffNum 2 c.m c.s k0 +
        (max (0 : ℤ) ((c.ua : ℤ) - (c.vq : ℤ) * (rq0 : ℤ) -
            (c.vg1 : ℤ) * ((rr0 - rq0 : ℕ) : ℤ) - (c.vh1 : ℤ) * ((2 * k0 - 1 - rr0 : ℕ) : ℤ)) -
          (c.vu : ℤ) * ((2 * k0 - 2 - rr0 - rq0 : ℕ) : ℤ) -
          (c.vlcq : ℤ) * ((rq0 - 2 : ℕ) : ℤ) -
          (c.vlcg1 : ℤ) * ((rr0 - rq0 - 4 : ℕ) : ℤ) -
          (c.vlch1 : ℤ) * ((2 * k0 - 1 - rr0 - 4 : ℕ) : ℤ) -
          (c.vrq : ℤ) * (resOrdExact 4 (2 * k0 - 1 - rr0) 2 rq0 : ℤ) -
          (c.vrf0q : ℤ) * (t3_2BVrf0Sub 2 k0 rq0 : ℤ) -
          (c.vrf0g1 : ℤ) * (t3_2BVrf0Sub 4 k0 (rr0 - rq0) : ℤ)) * mDen : ℚ) ≤ (c.unNum : ℚ) := by
      have hNatZ : (c.vx : ℤ) * (rkN : ℤ) + (h1 : ℤ) * mDen ≤ c.unNum + (subTot : ℤ) * mDen := by
        have h' : ((c.vx * rkN + h1 * mDenNat : ℕ) : ℤ) ≤ ((c.unNum.toNat + subTot * mDenNat : ℕ) : ℤ) := by
          exact_mod_cast hNat
        push_cast at h'
        rwa [hun_toNat] at h'
      have hrkZ : (rkN : ℤ) = rankDiffNum 2 c.m c.s k0 := rkDiffNat_cast 2 c.m c.s k0
      have hh1Z : (h1 : ℤ) = max (0 : ℤ) ((c.ua : ℤ) - (c.vq : ℤ) * (rq0 : ℤ) -
          (c.vg1 : ℤ) * ((rr0 - rq0 : ℕ) : ℤ) - (c.vh1 : ℤ) * ((2 * k0 - 1 - rr0 : ℕ) : ℤ)) := by
        dsimp only [h1]; rw [nat_sub_cast_eq_max_zero]; congr 1; push_cast; ring
      have hsubZ : (subTot : ℤ) =
          (c.vu : ℤ) * ((2 * k0 - 2 - rr0 - rq0 : ℕ) : ℤ) +
          (c.vlcq : ℤ) * ((rq0 - 2 : ℕ) : ℤ) +
          (c.vlcg1 : ℤ) * ((rr0 - rq0 - 4 : ℕ) : ℤ) +
          (c.vlch1 : ℤ) * ((2 * k0 - 1 - rr0 - 4 : ℕ) : ℤ) +
          (c.vrq : ℤ) * (resOrdExact 4 (2 * k0 - 1 - rr0) 2 rq0 : ℤ) +
          (c.vrf0q : ℤ) * (t3_2BVrf0Sub 2 k0 rq0 : ℤ) +
          (c.vrf0g1 : ℤ) * (t3_2BVrf0Sub 4 k0 (rr0 - rq0) : ℤ) := by
        simp only [subTot, baseSub, Nat.cast_add, Nat.cast_mul]
      have hb' : (c.vx : ℤ) * rankDiffNum 2 c.m c.s k0 +
          (max (0 : ℤ) ((c.ua : ℤ) - (c.vq : ℤ) * (rq0 : ℤ) -
              (c.vg1 : ℤ) * ((rr0 - rq0 : ℕ) : ℤ) - (c.vh1 : ℤ) * ((2 * k0 - 1 - rr0 : ℕ) : ℤ)) -
            (c.vu : ℤ) * ((2 * k0 - 2 - rr0 - rq0 : ℕ) : ℤ) -
            (c.vlcq : ℤ) * ((rq0 - 2 : ℕ) : ℤ) -
            (c.vlcg1 : ℤ) * ((rr0 - rq0 - 4 : ℕ) : ℤ) -
            (c.vlch1 : ℤ) * ((2 * k0 - 1 - rr0 - 4 : ℕ) : ℤ) -
            (c.vrq : ℤ) * (resOrdExact 4 (2 * k0 - 1 - rr0) 2 rq0 : ℤ) -
            (c.vrf0q : ℤ) * (t3_2BVrf0Sub 2 k0 rq0 : ℤ) -
            (c.vrf0g1 : ℤ) * (t3_2BVrf0Sub 4 k0 (rr0 - rq0) : ℤ)) * mDen ≤ c.unNum := by
        rw [hrkZ, hh1Z, hsubZ] at hNatZ
        linarith
      exact_mod_cast hb'
    push_cast [Int.cast_max] at hZ
    rw [← hrk_eq k0]
    have hdiv := div_le_div_of_nonneg_right hZ hmDenQ.le
    rw [add_div, mul_div_assoc, mul_div_cancel_right₀ _ hmDenQ.ne'] at hdiv
    linarith
  have hsl_mk : ∀ (rhs : ℤ), (c.vx : ℤ) * (rankDiffNum 2 c.m c.s 14 - rankDiffNum 2 c.m c.s 13) ≤ rhs * mDen →
      (c.vx : ℚ) * (rankDiffQ 2 c.m c.s 14 - rankDiffQ 2 c.m c.s 13) ≤ (rhs : ℚ) := by
    intro rhs hZ
    have hQ : (c.vx : ℚ) * ((rankDiffNum 2 c.m c.s 14 : ℚ) - (rankDiffNum 2 c.m c.s 13 : ℚ)) ≤ (rhs : ℚ) * (mDen : ℚ) := by
      exact_mod_cast hZ
    have hdiv := div_le_div_of_nonneg_right hQ hmDenQ.le
    rw [mul_div_cancel_right₀ _ hmDenQ.ne'] at hdiv
    have h3 : (c.vx : ℚ) * ((rankDiffNum 2 c.m c.s 14 : ℚ) - (rankDiffNum 2 c.m c.s 13 : ℚ)) / (mDen : ℚ) =
        (c.vx : ℚ) * (rankDiffQ 2 c.m c.s 14 - rankDiffQ 2 c.m c.s 13) := by
      rw [mul_sub, sub_div, mul_div_assoc, mul_div_assoc, hrk_eq 14, hrk_eq 13, ← mul_sub]
    linarith
  have hslA : (c.vx : ℚ) * (rankDiffQ 2 c.m c.s 14 - rankDiffQ 2 c.m c.s 13) ≤
      2 * (c.vu : ℚ) + 2 * (c.vlch1 : ℚ) + 4 * (c.vrq : ℚ) + 4 * (c.vrf0q : ℚ) + 8 * (c.vrf0g1 : ℚ) := by
    simpa using hsl_mk _ (decide_eq_true_eq.mp hsA)
  have hslB : (c.vx : ℚ) * (rankDiffQ 2 c.m c.s 14 - rankDiffQ 2 c.m c.s 13) ≤
      2 * (c.vlcg1 : ℚ) + 4 * (c.vrf0q : ℚ) + 30 * (c.vrf0g1 : ℚ) := by
    simpa using hsl_mk _ (decide_eq_true_eq.mp hsB)
  have hslC : (c.vx : ℚ) * (rankDiffQ 2 c.m c.s 14 - rankDiffQ 2 c.m c.s 13) ≤
      2 * (c.vlcq : ℚ) + 8 * (c.vrq : ℚ) + 26 * (c.vrf0q : ℚ) + 8 * (c.vrf0g1 : ℚ) := by
    simpa using hsl_mk _ (decide_eq_true_eq.mp hsC)
  have hslD : (c.vx : ℚ) * (rankDiffQ 2 c.m c.s 14 - rankDiffQ 2 c.m c.s 13) ≤
      (c.vlcq : ℚ) + (c.vlch1 : ℚ) + 6 * (c.vrq : ℚ) + 15 * (c.vrf0q : ℚ) + 8 * (c.vrf0g1 : ℚ) := by
    simpa using hsl_mk _ (decide_eq_true_eq.mp hsD)
  -- Exact 4-ray decomposition for ALL unbounded k0 ≥ 14!
  have hpt_all : ∀ (k0 rr0 rq0 : ℕ) (hrr0 : rr0 ≤ 2 * k0) (hrq0 : rq0 ≤ rr0) (α : ℚ), (α = 0 ∨ α = 1) →
      (c.vx : ℚ) * rankDiffQ 2 c.m c.s k0 + (c.ua : ℚ) * α ≤
      (c.unNum : ℚ) / (mDen : ℚ) +
      (c.vq : ℚ) * (α * (rq0 : ℚ)) + (c.vg1 : ℚ) * (α * ((rr0 - rq0 : ℕ) : ℚ)) + (c.vh1 : ℚ) * (α * ((2 * k0 - 1 - rr0 : ℕ) : ℚ)) +
      (c.vu : ℚ) * ((2 * k0 - 2 - rr0 - rq0 : ℕ) : ℚ) +
      (c.vlcq : ℚ) * ((rq0 - 2 : ℕ) : ℚ) +
      (c.vlcg1 : ℚ) * ((rr0 - rq0 - 4 : ℕ) : ℚ) +
      (c.vlch1 : ℚ) * ((2 * k0 - 1 - rr0 - 4 : ℕ) : ℚ) +
      (c.vrq : ℚ) * (resOrdExact 4 (2 * k0 - 1 - rr0) 2 rq0 : ℚ) +
      (c.vrf0q : ℚ) * (t3_2BVrf0Sub 2 k0 rq0 : ℚ) +
      (c.vrf0g1 : ℚ) * (t3_2BVrf0Sub 4 k0 (rr0 - rq0) : ℚ) := by
    intro k0 rr0 rq0 hrr0 hrq0 α hα
    have hα_max : (c.ua : ℚ) * α - (c.vq : ℚ) * (α * (rq0 : ℚ)) - (c.vg1 : ℚ) * (α * ((rr0 - rq0 : ℕ) : ℚ)) -
        (c.vh1 : ℚ) * (α * ((2 * k0 - 1 - rr0 : ℕ) : ℚ)) ≤
        max (0 : ℚ) ((c.ua : ℚ) - (c.vq : ℚ) * (rq0 : ℚ) - (c.vg1 : ℚ) * ((rr0 - rq0 : ℕ) : ℚ) -
          (c.vh1 : ℚ) * ((2 * k0 - 1 - rr0 : ℕ) : ℚ)) := by
      rcases hα with rfl | rfl
      · simp only [mul_zero, zero_mul, sub_zero, le_max_left]
      · simp only [mul_one, one_mul, le_max_right]
    by_cases hk0 : k0 ≤ 14
    · linarith [hpt_le k0 hk0 rr0 hrr0 rq0 hrq0]
    · have hgt : 14 ≤ k0 := by omega
      set a : ℕ := 2 * k0 - rr0
      set b : ℕ := rr0 - rq0
      set d : ℕ := rq0
      have habd : a + b + d = 2 * k0 := by omega
      set Δ : ℕ := 2 * k0 - 28
      -- Step 1: reduce b down to at most 4
      set q1 : ℕ := min (b - 4) Δ
      set b0 : ℕ := b - q1
      set Δ1 : ℕ := Δ - q1
      -- Step 2: decompose Δ1 into (p, q2, r) with a = a0 + p + r, d = d0 + q2 + r, p + q2 + 2*r = Δ1
      have hdecomp : ∃ (a0 d0 p q2 r : ℕ),
          a0 + b0 + d0 = 28 ∧
          a = a0 + p + r ∧ d = d0 + q2 + r ∧
          p + q1 + q2 + 2 * r = 2 * (k0 - 14) ∧
          (0 < p + r → 5 ≤ a0) ∧
          (0 < q2 + r → 2 ≤ d0) ∧
          (a0 - 2 - d0) + p ≤ a - 2 - d := by
        have hsum_b0 : a + b0 + d = 28 + Δ1 := by dsimp [b0, Δ1, q1, Δ] at *; omega
        by_cases hΔ1 : Δ1 = 0
        · refine ⟨a, d, 0, 0, 0, by omega, by omega, by omega, by dsimp [Δ1, Δ] at hΔ1 ⊢; omega, by omega, by omega, by omega⟩
        · have hb0_le : b0 ≤ 4 := by dsimp [b0, q1, Δ1] at hΔ1 ⊢; omega
          have hstep_base : q1 + Δ1 = 2 * (k0 - 14) := by dsimp [q1, Δ1, Δ]; omega
          by_cases hA : d + 2 + Δ1 ≤ a
          · refine ⟨a - Δ1, d, Δ1, 0, 0, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
          · by_cases hC : a + Δ1 ≤ d + 2
            · refine ⟨a, d - Δ1, 0, Δ1, 0, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
            · by_cases hpar : b0 % 2 = 0
              · by_cases hge2 : d + 2 ≤ a
                · set p := a - d - 2
                  have heven : (Δ1 - p) % 2 = 0 := by omega
                  set r := (Δ1 - p) / 2
                  refine ⟨a - p - r, d - r, p, 0, r, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · set q2 := d + 2 - a
                  have heven : (Δ1 - q2) % 2 = 0 := by omega
                  set r := (Δ1 - q2) / 2
                  refine ⟨a - r, d - q2 - r, 0, q2, r, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
              · by_cases hge3 : d + 3 ≤ a
                · set p := a - d - 3
                  have heven : (Δ1 - p) % 2 = 0 := by omega
                  set r := (Δ1 - p) / 2
                  refine ⟨a - p - r, d - r, p, 0, r, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
                · set q2 := d + 1 - a
                  have heven : (Δ1 - q2) % 2 = 0 := by omega
                  set r := (Δ1 - q2) / 2
                  refine ⟨a - r, d - q2 - r, 0, q2, r, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      obtain ⟨a0, d0, p, q2, r, hsum0, ha_eq, hd_eq, hstep_eq, ha_h, hd_h, hvu_h⟩ := hdecomp
      set rrB : ℕ := b0 + d0
      have hrrB_le : rrB ≤ 28 := by omega
      have hd0_le : d0 ≤ rrB := by omega
      have hbase := hpt_le 14 le_rfl rrB hrrB_le d0 hd0_le
      have ha0_eq : 28 - rrB = a0 := by omega
      have hb0_eq : rrB - d0 = b0 := by omega
      have hmax_mono : max (0 : ℚ) ((c.ua : ℚ) - (c.vq : ℚ) * (rq0 : ℚ) - (c.vg1 : ℚ) * ((rr0 - rq0 : ℕ) : ℚ) -
            (c.vh1 : ℚ) * ((2 * k0 - 1 - rr0 : ℕ) : ℚ)) ≤
          max (0 : ℚ) ((c.ua : ℚ) - (c.vq : ℚ) * (d0 : ℚ) - (c.vg1 : ℚ) * ((rrB - d0 : ℕ) : ℚ) -
            (c.vh1 : ℚ) * ((2 * 14 - 1 - rrB : ℕ) : ℚ)) := by
        apply max_le (le_max_left _ _)
        refine le_trans ?_ (le_max_right _ _)
        have h1 : (d0 : ℚ) ≤ (rq0 : ℚ) := by exact_mod_cast (by omega : d0 ≤ rq0)
        have h2 : ((rrB - d0 : ℕ) : ℚ) ≤ ((rr0 - rq0 : ℕ) : ℚ) := by exact_mod_cast (by omega : rrB - d0 ≤ rr0 - rq0)
        have h3 : ((2 * 14 - 1 - rrB : ℕ) : ℚ) ≤ ((2 * k0 - 1 - rr0 : ℕ) : ℚ) := by exact_mod_cast (by omega : 2 * 14 - 1 - rrB ≤ 2 * k0 - 1 - rr0)
        have hm1 := mul_le_mul_of_nonneg_left h1 (show (0 : ℚ) ≤ (c.vq : ℚ) by positivity)
        have hm2 := mul_le_mul_of_nonneg_left h2 (show (0 : ℚ) ≤ (c.vg1 : ℚ) by positivity)
        have hm3 := mul_le_mul_of_nonneg_left h3 (show (0 : ℚ) ≤ (c.vh1 : ℚ) by positivity)
        linarith only [hm1, hm2, hm3]
      have htail_rk := rankDiffQ_le_linear_tail 2 c.m c.s 14 k0 (by omega) hgt
      have hstep_split : ((k0 - 14 : ℕ) : ℚ) = (p : ℚ) / 2 + (q1 : ℚ) / 2 + (q2 : ℚ) / 2 + (r : ℚ) := by
        have : (p : ℚ) + (q1 : ℚ) + (q2 : ℚ) + 2 * (r : ℚ) = 2 * ((k0 - 14 : ℕ) : ℚ) := by exact_mod_cast hstep_eq
        linarith
      -- Check growth of every term!
      have hvu_g : ((2 * 14 - 2 - rrB - d0 : ℕ) : ℚ) + (p : ℚ) ≤ ((2 * k0 - 2 - rr0 - rq0 : ℕ) : ℚ) := by
        have hvu_eq1 : 2 * 14 - 2 - rrB - d0 = a0 - 2 - d0 := by clear * - ha0_eq hrrB_le; omega
        have hvu_eq2 : 2 * k0 - 2 - rr0 - rq0 = a - 2 - d := by clear * - hrr0; dsimp [a, d]; omega
        rw [hvu_eq1, hvu_eq2]; exact_mod_cast hvu_h
      have hlcq_g : ((d0 - 2 : ℕ) : ℚ) + (q2 : ℚ) + (r : ℚ) ≤ ((rq0 - 2 : ℕ) : ℚ) := by
        have hd_d : d0 + q2 + r = rq0 := by clear * - hd_eq; dsimp [d] at hd_eq; omega
        by_cases h0 : q2 + r = 0
        · have : q2 = 0 ∧ r = 0 := by omega
          rw [this.1, this.2, Nat.cast_zero, add_zero, add_zero]
          exact_mod_cast (by clear * - hd_d; omega : d0 - 2 ≤ rq0 - 2)
        · have hd2 := hd_h (Nat.pos_of_ne_zero h0)
          exact_mod_cast (by clear * - hd_d hd2; omega : (d0 - 2) + q2 + r ≤ rq0 - 2)
      have hlcg1_g : ((rrB - d0 - 4 : ℕ) : ℚ) + (q1 : ℚ) ≤ ((rr0 - rq0 - 4 : ℕ) : ℚ) := by
        have hb_d : rrB - d0 + q1 = rr0 - rq0 := by
          clear * - hb0_eq hrr0 hrq0 hgt; dsimp [b0, b, q1, Δ] at hb0_eq ⊢; omega
        by_cases h0 : q1 = 0
        · rw [h0, Nat.cast_zero, add_zero]
          exact_mod_cast (by clear * - hb_d; omega : rrB - d0 - 4 ≤ rr0 - rq0 - 4)
        · have hb4 : 4 ≤ rrB - d0 := by
            clear * - hb0_eq h0; dsimp [b0, q1] at hb0_eq h0 ⊢; omega
          exact_mod_cast (by clear * - hb_d hb4; omega : (rrB - d0 - 4) + q1 ≤ rr0 - rq0 - 4)
      have hlch1_g : ((2 * 14 - 1 - rrB - 4 : ℕ) : ℚ) + (p : ℚ) + (r : ℚ) ≤ ((2 * k0 - 1 - rr0 - 4 : ℕ) : ℚ) := by
        have ha_d : a0 + p + r = 2 * k0 - rr0 := by
          clear * - ha_eq hrr0 hgt; dsimp [a] at ha_eq; omega
        have heq1 : 2 * 14 - 1 - rrB = a0 - 1 := by clear * - ha0_eq hrrB_le; omega
        have heq2 : 2 * k0 - 1 - rr0 = 2 * k0 - rr0 - 1 := by omega
        by_cases h0 : p + r = 0
        · have : p = 0 ∧ r = 0 := by omega
          rw [this.1, this.2, Nat.cast_zero, add_zero, add_zero]
          exact_mod_cast (by clear * - ha_d heq1 heq2; omega : 2 * 14 - 1 - rrB - 4 ≤ 2 * k0 - 1 - rr0 - 4)
        · have ha5 := ha_h (Nat.pos_of_ne_zero h0)
          exact_mod_cast (by clear * - ha_d heq1 heq2 ha5; omega : (2 * 14 - 1 - rrB - 4) + p + r ≤ 2 * k0 - 1 - rr0 - 4)
      have hrq_g : (resOrdExact 4 (2 * 14 - 1 - rrB) 2 d0 : ℚ) + 2 * (p : ℚ) + 4 * (q2 : ℚ) + 6 * (r : ℚ) ≤
          (resOrdExact 4 (2 * k0 - 1 - rr0) 2 rq0 : ℚ) := by
        have h1 : 2 * 14 - 1 - rrB = a0 - 1 := by omega
        have h2 : 2 * k0 - 1 - rr0 = a0 + p + r - 1 := by omega
        have h3 : rq0 = d0 + q2 + r := by omega
        rw [h1, h2, h3]
        exact_mod_cast resOrdExact_4_2_grow a0 d0 p q2 r ha_h hd_h
      have hrf0q_g : (t3_2BVrf0Sub 2 14 d0 : ℚ) + 2 * (p : ℚ) + 2 * (q1 : ℚ) + 13 * (q2 : ℚ) + 15 * (r : ℚ) ≤
          (t3_2BVrf0Sub 2 k0 rq0 : ℚ) := by
        rw [t3_2BVrf0Sub_eq_large 2 14 d0 (Or.inl rfl) le_rfl, t3_2BVrf0Sub_eq_large 2 k0 rq0 (Or.inl rfl) hgt]
        have hnat : (2 * 2 * 14 + 11 * d0 - 11 * 2) + 2 * p + 2 * q1 + 13 * q2 + 15 * r ≤
            2 * 2 * k0 + 11 * rq0 - 11 * 2 := by
          clear * - hgt hstep_eq hd_eq
          dsimp [d] at hd_eq; omega
        exact_mod_cast hnat
      have hrf0g1_g : (t3_2BVrf0Sub 4 14 (rrB - d0) : ℚ) + 4 * (p : ℚ) + 15 * (q1 : ℚ) + 4 * (q2 : ℚ) + 8 * (r : ℚ) ≤
          (t3_2BVrf0Sub 4 k0 (rr0 - rq0) : ℚ) := by
        rw [t3_2BVrf0Sub_eq_large 4 14 (rrB - d0) (Or.inr rfl) le_rfl,
          t3_2BVrf0Sub_eq_large 4 k0 (rr0 - rq0) (Or.inr rfl) hgt]
        have hnat : (2 * 4 * 14 + 11 * (rrB - d0) - 11 * 4) + 4 * p + 15 * q1 + 4 * q2 + 8 * r ≤
            2 * 4 * k0 + 11 * (rr0 - rq0) - 11 * 4 := by
          have hb_eq : rr0 - rq0 = (rrB - d0) + q1 := by
            clear * - hb0_eq hrr0 hrq0 hgt
            dsimp [b0, b, q1, Δ] at hb0_eq ⊢; omega
          clear * - hgt hstep_eq hb_eq; omega
        exact_mod_cast hnat
      have hrk_mul := mul_le_mul_of_nonneg_left htail_rk (show (0 : ℚ) ≤ (c.vx : ℚ) by positivity)
      have hA := mul_le_mul_of_nonneg_right hslA (show (0 : ℚ) ≤ (p : ℚ) / 2 by positivity)
      have hB := mul_le_mul_of_nonneg_right hslB (show (0 : ℚ) ≤ (q1 : ℚ) / 2 by positivity)
      have hC := mul_le_mul_of_nonneg_right hslC (show (0 : ℚ) ≤ (q2 : ℚ) / 2 by positivity)
      have hD := mul_le_mul_of_nonneg_right hslD (show (0 : ℚ) ≤ (r : ℚ) by positivity)
      have hcomb_sl : (c.vx : ℚ) * (rankDiffQ 2 c.m c.s 14 - rankDiffQ 2 c.m c.s 13) * ((k0 - 14 : ℕ) : ℚ) ≤
          (c.vu : ℚ) * (p : ℚ) + (c.vlcq : ℚ) * ((q2 : ℚ) + (r : ℚ)) + (c.vlcg1 : ℚ) * (q1 : ℚ) +
          (c.vlch1 : ℚ) * ((p : ℚ) + (r : ℚ)) +
          (c.vrq : ℚ) * (2 * (p : ℚ) + 4 * (q2 : ℚ) + 6 * (r : ℚ)) +
          (c.vrf0q : ℚ) * (2 * (p : ℚ) + 2 * (q1 : ℚ) + 13 * (q2 : ℚ) + 15 * (r : ℚ)) +
          (c.vrf0g1 : ℚ) * (4 * (p : ℚ) + 15 * (q1 : ℚ) + 4 * (q2 : ℚ) + 8 * (r : ℚ)) := by
        rw [hstep_split]; linarith only [hA, hB, hC, hD]
      have hm1 := mul_le_mul_of_nonneg_left hvu_g (show (0 : ℚ) ≤ (c.vu : ℚ) by positivity)
      have hm2 := mul_le_mul_of_nonneg_left hlcq_g (show (0 : ℚ) ≤ (c.vlcq : ℚ) by positivity)
      have hm3 := mul_le_mul_of_nonneg_left hlcg1_g (show (0 : ℚ) ≤ (c.vlcg1 : ℚ) by positivity)
      have hm4 := mul_le_mul_of_nonneg_left hlch1_g (show (0 : ℚ) ≤ (c.vlch1 : ℚ) by positivity)
      have hm5 := mul_le_mul_of_nonneg_left hrq_g (show (0 : ℚ) ≤ (c.vrq : ℚ) by positivity)
      have hm6 := mul_le_mul_of_nonneg_left hrf0q_g (show (0 : ℚ) ≤ (c.vrf0q : ℚ) by positivity)
      have hm7 := mul_le_mul_of_nonneg_left hrf0g1_g (show (0 : ℚ) ≤ (c.vrf0g1 : ℚ) by positivity)
      linarith only [hα_max, hbase, hmax_mono, hrk_mul, hcomb_sl, hm1, hm2, hm3, hm4, hm5, hm6, hm7]
  -- Step 2: Sum over i : Idx and divide by N!
  let L (x y z : ℚ) : ℚ :=
    (c.unNum : ℚ) / (mDen : ℚ) - (c.ua : ℚ) * ((A : ℚ) / (N : ℚ)) +
    (c.vq : ℚ) * (z * (wY : ℚ) / (N : ℚ)) +
    (c.vg1 : ℚ) * ((y - z) * (wY : ℚ) / (N : ℚ)) +
    (c.vh1 : ℚ) * (((x - 1 - y) * (wY : ℚ) + 1) / (N : ℚ)) +
    (c.vu : ℚ) * (((x - 2 - y - z) * (wY : ℚ) + 2) / (N : ℚ)) +
    (c.vlcq : ℚ) * ((z - 2) * (wY : ℚ) / (N : ℚ)) +
    (c.vlcg1 : ℚ) * ((y - z - 4) * (wY : ℚ) / (N : ℚ)) +
    (c.vlch1 : ℚ) * (((x - 5 - y) * (wY : ℚ) + 1) / (N : ℚ)) +
    (c.vrq : ℚ) * (((2 * (x - 1 - y) + 4 * z - 8) * (wY : ℚ) + 2) / (N : ℚ)) +
    (c.vrf0q : ℚ) * ((2 * (x - 11) + 11 * z) * (wY : ℚ) / (N : ℚ)) +
    (c.vrf0g1 : ℚ) * ((4 * (x - 11) + 11 * (y - z)) * (wY : ℚ) / (N : ℚ))
  have hsum_all : (c.vx : ℚ) * ((∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) / (N : ℚ)) ≤ L cVal cgVal cqVal := by
    have hpt_i : ∀ i : Idx,
        (c.vx : ℚ) * rankDiffQ 2 c.m c.s (k i) + (c.ua : ℚ) * (if i ∈ Az then (1 : ℚ) else 0) ≤
        (c.unNum : ℚ) / (mDen : ℚ) +
        (c.vq : ℚ) * ((if i ∈ Az then (1 : ℚ) else 0) * (rq i : ℚ)) +
        (c.vg1 : ℚ) * ((if i ∈ Az then (1 : ℚ) else 0) * ((rr i - rq i : ℕ) : ℚ)) +
        (c.vh1 : ℚ) * ((if i ∈ Az then (1 : ℚ) else 0) * ((2 * k i - 1 - rr i : ℕ) : ℚ)) +
        (c.vu : ℚ) * ((2 * k i - 2 - rr i - rq i : ℕ) : ℚ) +
        (c.vlcq : ℚ) * ((rq i - 2 : ℕ) : ℚ) +
        (c.vlcg1 : ℚ) * ((rr i - rq i - 4 : ℕ) : ℚ) +
        (c.vlch1 : ℚ) * ((2 * k i - 1 - rr i - 4 : ℕ) : ℚ) +
        (c.vrq : ℚ) * (resOrdExact 4 (2 * k i - 1 - rr i) 2 (rq i) : ℚ) +
        (c.vrf0q : ℚ) * (t3_2BVrf0Sub 2 (k i) (rq i) : ℚ) +
        (c.vrf0g1 : ℚ) * (t3_2BVrf0Sub 4 (k i) (rr i - rq i) : ℚ) :=
      fun i => hpt_all (k i) (rr i) (rq i) (hrr_le i) (hrq_le i)
        (if i ∈ Az then 1 else 0) (by split_ifs <;> simp)
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt_i i
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hcardIdx] at hsum
    have hAz_sum : (∑ i : Idx, if i ∈ Az then (1 : ℚ) else 0) = (Az.card : ℚ) := by simp [Finset.sum_ite_mem]
    have hq_sum : (∑ i : Idx, (if i ∈ Az then (1 : ℚ) else 0) * (rq i : ℚ)) = ∑ i ∈ Az, (rq i : ℚ) := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    have hg1_sum : (∑ i : Idx, (if i ∈ Az then (1 : ℚ) else 0) * ((rr i - rq i : ℕ) : ℚ)) =
        ∑ i ∈ Az, ((rr i - rq i : ℕ) : ℚ) := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    have hh1_sum : (∑ i : Idx, (if i ∈ Az then (1 : ℚ) else 0) * ((2 * k i - 1 - rr i : ℕ) : ℚ)) =
        ∑ i ∈ Az, ((2 * k i - 1 - rr i : ℕ) : ℚ) := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    rw [hAz_sum, hq_sum, hg1_sum, hh1_sum] at hsum
    have hAzQ : (A : ℚ) ≤ (Az.card : ℚ) := by exact_mod_cast hAz
    have hcomb : (c.vx : ℚ) * (∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) ≤ (N : ℚ) * L cVal cgVal cqVal := by
      have hNL : (N : ℚ) * L cVal cgVal cqVal =
          (N : ℚ) * ((c.unNum : ℚ) / (mDen : ℚ)) - (c.ua : ℚ) * (A : ℚ) +
          (c.vq : ℚ) * (cqVal * (wY : ℚ)) +
          (c.vg1 : ℚ) * ((cgVal - cqVal) * (wY : ℚ)) +
          (c.vh1 : ℚ) * ((cVal - 1 - cgVal) * (wY : ℚ) + 1) +
          (c.vu : ℚ) * ((cVal - 2 - cgVal - cqVal) * (wY : ℚ) + 2) +
          (c.vlcq : ℚ) * ((cqVal - 2) * (wY : ℚ)) +
          (c.vlcg1 : ℚ) * ((cgVal - cqVal - 4) * (wY : ℚ)) +
          (c.vlch1 : ℚ) * ((cVal - 5 - cgVal) * (wY : ℚ) + 1) +
          (c.vrq : ℚ) * ((2 * (cVal - 1 - cgVal) + 4 * cqVal - 8) * (wY : ℚ) + 2) +
          (c.vrf0q : ℚ) * ((2 * (cVal - 11) + 11 * cqVal) * (wY : ℚ)) +
          (c.vrf0g1 : ℚ) * ((4 * (cVal - 11) + 11 * (cgVal - cqVal)) * (wY : ℚ)) := by
        have hmN : ∀ a b : ℚ, (N : ℚ) * (a * (b / (N : ℚ))) = a * b := fun a b => by
          rw [← mul_assoc, mul_comm (N : ℚ) a, mul_assoc, mul_div_cancel₀ _ hNQ.ne']
        dsimp only [L]; simp only [mul_add, mul_sub, hmN]
      rw [hNL]
      have ha := mul_le_mul_of_nonneg_left hAzQ (show (0 : ℚ) ≤ (c.ua : ℚ) by positivity)
      have h1 := mul_le_mul_of_nonneg_left hq (show (0 : ℚ) ≤ (c.vq : ℚ) by positivity)
      have h2 := mul_le_mul_of_nonneg_left hg1 (show (0 : ℚ) ≤ (c.vg1 : ℚ) by positivity)
      have h3 := mul_le_mul_of_nonneg_left hh1 (show (0 : ℚ) ≤ (c.vh1 : ℚ) by positivity)
      have h4 := mul_le_mul_of_nonneg_left hu (show (0 : ℚ) ≤ (c.vu : ℚ) by positivity)
      have h5 := mul_le_mul_of_nonneg_left hlcq (show (0 : ℚ) ≤ (c.vlcq : ℚ) by positivity)
      have h6 := mul_le_mul_of_nonneg_left hlcg1 (show (0 : ℚ) ≤ (c.vlcg1 : ℚ) by positivity)
      have h7 := mul_le_mul_of_nonneg_left hlch1 (show (0 : ℚ) ≤ (c.vlch1 : ℚ) by positivity)
      have h8 := mul_le_mul_of_nonneg_left hrq_res (show (0 : ℚ) ≤ (c.vrq : ℚ) by positivity)
      have h9 := mul_le_mul_of_nonneg_left hrf0q (show (0 : ℚ) ≤ (c.vrf0q : ℚ) by positivity)
      have h10 := mul_le_mul_of_nonneg_left hrf0g1 (show (0 : ℚ) ≤ (c.vrf0g1 : ℚ) by positivity)
      linarith only [hsum, ha, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    rw [← mul_div_assoc, div_le_iff₀' hNQ]
    exact hcomb
  -- Step 3: Decode triangle vertices at cLo & cHi + barycentric convex combination!
  have hL_corner : ∀ (cNum cDen cgNum cgDen cqNum cqDen : ℕ)
      (hcD : 0 < cDen) (hcgD : 0 < cgDen) (hcqD : 0 < cqDen),
      checkT3_2BCorner c cNum cDen cgNum cgDen cqNum cqDen = true →
      (c.m = 0 → L ((cNum : ℚ) / (cDen : ℚ)) ((cgNum : ℚ) / (cgDen : ℚ)) ((cqNum : ℚ) / (cqDen : ℚ)) < 0) ∧
      (0 < c.m → L ((cNum : ℚ) / (cDen : ℚ)) ((cgNum : ℚ) / (cgDen : ℚ)) ((cqNum : ℚ) / (cqDen : ℚ)) -
          (c.vx : ℚ) * vquotLbQ 2 c.m c.s ((cNum : ℚ) / (cDen : ℚ)) <
        -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ))) := by
    intro cNum cDen cgNum cgDen cqNum cqDen hcD hcgD hcqD hep
    have hcDQ : (0 : ℚ) < (cDen : ℚ) := by exact_mod_cast hcD
    have hcgDQ : (0 : ℚ) < (cgDen : ℚ) := by exact_mod_cast hcgD
    have hcqDQ : (0 : ℚ) < (cqDen : ℚ) := by exact_mod_cast hcqD
    unfold checkT3_2BCorner at hep; dsimp only at hep
    set uZ : ℤ := (cDen : ℤ) * (cgDen : ℤ) * (cqDen : ℤ)
    set cZ : ℤ := (cNum : ℤ) * (cgDen : ℤ) * (cqDen : ℤ)
    set cgZ : ℤ := (cgNum : ℤ) * (cDen : ℤ) * (cqDen : ℤ)
    set cqZ : ℤ := (cqNum : ℤ) * (cDen : ℤ) * (cgDen : ℤ)
    set linZ : ℤ :=
      -(c.ua : ℤ) * (A : ℤ) * uZ +
      (c.vq : ℤ) * (cqZ * (wY : ℤ)) +
      (c.vg1 : ℤ) * ((cgZ - cqZ) * (wY : ℤ)) +
      (c.vh1 : ℤ) * ((cZ - uZ - cgZ) * (wY : ℤ) + uZ) +
      (c.vu : ℤ) * ((cZ - 2 * uZ - cgZ - cqZ) * (wY : ℤ) + 2 * uZ) +
      (c.vlcq : ℤ) * ((cqZ - 2 * uZ) * (wY : ℤ)) +
      (c.vlcg1 : ℤ) * ((cgZ - cqZ - 4 * uZ) * (wY : ℤ)) +
      (c.vlch1 : ℤ) * ((cZ - 5 * uZ - cgZ) * (wY : ℤ) + uZ) +
      (c.vrq : ℤ) * ((2 * (cZ - uZ - cgZ) + 4 * cqZ - 8 * uZ) * (wY : ℤ) + 2 * uZ) +
      (c.vrf0q : ℤ) * ((2 * (cZ - 11 * uZ) + 11 * cqZ) * (wY : ℤ)) +
      (c.vrf0g1 : ℤ) * ((4 * (cZ - 11 * uZ) + 11 * (cgZ - cqZ)) * (wY : ℤ))
    have huQ : (uZ : ℚ) = (cDen : ℚ) * (cgDen : ℚ) * (cqDen : ℚ) := by dsimp [uZ]; push_cast; ring
    have huPos : (0 : ℚ) < (uZ : ℚ) := by rw [huQ]; positivity
    have hL_eq : L ((cNum : ℚ) / (cDen : ℚ)) ((cgNum : ℚ) / (cgDen : ℚ)) ((cqNum : ℚ) / (cqDen : ℚ)) =
        ((c.unNum : ℚ) * (N : ℚ) * (uZ : ℚ) + (linZ : ℚ) * (mDen : ℚ)) / ((N : ℚ) * (mDen : ℚ) * (uZ : ℚ)) := by
      have hc_eq : (cNum : ℚ) / (cDen : ℚ) = (cZ : ℚ) / (uZ : ℚ) := by
        dsimp only [cZ, uZ]; push_cast; field_simp [hcDQ.ne', hcgDQ.ne', hcqDQ.ne']
      have hcg_eq : (cgNum : ℚ) / (cgDen : ℚ) = (cgZ : ℚ) / (uZ : ℚ) := by
        dsimp only [cgZ, uZ]; push_cast; field_simp [hcDQ.ne', hcgDQ.ne', hcqDQ.ne']
      have hcq_eq : (cqNum : ℚ) / (cqDen : ℚ) = (cqZ : ℚ) / (uZ : ℚ) := by
        dsimp only [cqZ, uZ]; push_cast; field_simp [hcDQ.ne', hcgDQ.ne', hcqDQ.ne']
      rw [hc_eq, hcg_eq, hcq_eq, eq_div_iff (by positivity)]
      set cQ : ℚ := (cZ : ℚ); set cgQ : ℚ := (cgZ : ℚ); set cqQ : ℚ := (cqZ : ℚ); set uQ : ℚ := (uZ : ℚ)
      have huQ_ne : uQ ≠ 0 := huPos.ne'
      have hcl : ∀ a b : ℚ, (a * (b / (N : ℚ))) * ((N : ℚ) * (mDen : ℚ) * uQ) = (a * (b * uQ)) * (mDen : ℚ) :=
        fun a b => by field_simp [hNQ.ne']
      have h0 : ((c.unNum : ℚ) / (mDen : ℚ)) * ((N : ℚ) * (mDen : ℚ) * uQ) = (c.unNum : ℚ) * (N : ℚ) * uQ := by
        field_simp [hmDenQ.ne']
      have ha : ((c.ua : ℚ) * ((A : ℚ) / (N : ℚ))) * ((N : ℚ) * (mDen : ℚ) * uQ) = ((c.ua : ℚ) * (A : ℚ) * uQ) * (mDen : ℚ) := by
        rw [hcl]; ring
      have h1 : (cqQ / uQ * (wY : ℚ)) * uQ = cqQ * (wY : ℚ) := by field_simp [huQ_ne]
      have h2 : ((cgQ / uQ - cqQ / uQ) * (wY : ℚ)) * uQ = (cgQ - cqQ) * (wY : ℚ) := by field_simp [huQ_ne]
      have h3 : ((cQ / uQ - 1 - cgQ / uQ) * (wY : ℚ) + 1) * uQ = (cQ - uQ - cgQ) * (wY : ℚ) + uQ := by
        field_simp [huQ_ne]
      have h4 : ((cQ / uQ - 2 - cgQ / uQ - cqQ / uQ) * (wY : ℚ) + 2) * uQ = (cQ - 2 * uQ - cgQ - cqQ) * (wY : ℚ) + 2 * uQ := by
        field_simp [huQ_ne]
      have h5 : ((cqQ / uQ - 2) * (wY : ℚ)) * uQ = (cqQ - 2 * uQ) * (wY : ℚ) := by field_simp [huQ_ne]
      have h6 : ((cgQ / uQ - cqQ / uQ - 4) * (wY : ℚ)) * uQ = (cgQ - cqQ - 4 * uQ) * (wY : ℚ) := by field_simp [huQ_ne]
      have h7 : ((cQ / uQ - 5 - cgQ / uQ) * (wY : ℚ) + 1) * uQ = (cQ - 5 * uQ - cgQ) * (wY : ℚ) + uQ := by
        field_simp [huQ_ne]
      have h8 : ((2 * (cQ / uQ - 1 - cgQ / uQ) + 4 * (cqQ / uQ) - 8) * (wY : ℚ) + 2) * uQ =
          (2 * (cQ - uQ - cgQ) + 4 * cqQ - 8 * uQ) * (wY : ℚ) + 2 * uQ := by field_simp [huQ_ne]
      have h9 : ((2 * (cQ / uQ - 11) + 11 * (cqQ / uQ)) * (wY : ℚ)) * uQ = (2 * (cQ - 11 * uQ) + 11 * cqQ) * (wY : ℚ) := by
        field_simp [huQ_ne]
      have h10 : ((4 * (cQ / uQ - 11) + 11 * (cgQ / uQ - cqQ / uQ)) * (wY : ℚ)) * uQ =
          (4 * (cQ - 11 * uQ) + 11 * (cgQ - cqQ)) * (wY : ℚ) := by field_simp [huQ_ne]
      have hlinQ : (linZ : ℚ) =
          -(c.ua : ℚ) * (A : ℚ) * uQ +
          (c.vq : ℚ) * (cqQ * (wY : ℚ)) +
          (c.vg1 : ℚ) * ((cgQ - cqQ) * (wY : ℚ)) +
          (c.vh1 : ℚ) * ((cQ - uQ - cgQ) * (wY : ℚ) + uQ) +
          (c.vu : ℚ) * ((cQ - 2 * uQ - cgQ - cqQ) * (wY : ℚ) + 2 * uQ) +
          (c.vlcq : ℚ) * ((cqQ - 2 * uQ) * (wY : ℚ)) +
          (c.vlcg1 : ℚ) * ((cgQ - cqQ - 4 * uQ) * (wY : ℚ)) +
          (c.vlch1 : ℚ) * ((cQ - 5 * uQ - cgQ) * (wY : ℚ) + uQ) +
          (c.vrq : ℚ) * ((2 * (cQ - uQ - cgQ) + 4 * cqQ - 8 * uQ) * (wY : ℚ) + 2 * uQ) +
          (c.vrf0q : ℚ) * ((2 * (cQ - 11 * uQ) + 11 * cqQ) * (wY : ℚ)) +
          (c.vrf0g1 : ℚ) * ((4 * (cQ - 11 * uQ) + 11 * (cgQ - cqQ)) * (wY : ℚ)) := by
        dsimp only [linZ, cQ, cgQ, cqQ, uQ]; push_cast; rfl
      dsimp only [L]
      rw [hlinQ]
      have htop : ∀ x y : ℚ, (x + y) * ((N : ℚ) * (mDen : ℚ) * uQ) =
          x * ((N : ℚ) * (mDen : ℚ) * uQ) + y * ((N : ℚ) * (mDen : ℚ) * uQ) := fun _ _ => add_mul _ _ _
      have htopS : ∀ x y : ℚ, (x - y) * ((N : ℚ) * (mDen : ℚ) * uQ) =
          x * ((N : ℚ) * (mDen : ℚ) * uQ) - y * ((N : ℚ) * (mDen : ℚ) * uQ) := fun _ _ => sub_mul _ _ _
      have hrmul : ∀ x y : ℚ, (x + y) * (mDen : ℚ) = x * (mDen : ℚ) + y * (mDen : ℚ) := fun _ _ => add_mul _ _ _
      conv_lhs =>
        rw [htop, htop, htop, htop, htop, htop, htop, htop, htop, htop, htopS]
        rw [h0, ha, hcl, hcl, hcl, hcl, hcl, hcl, hcl, hcl, hcl, hcl]
        rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
      conv_rhs =>
        rw [hrmul, hrmul, hrmul, hrmul, hrmul, hrmul, hrmul, hrmul, hrmul, hrmul]
      simp only [neg_mul, sub_eq_add_neg, add_assoc]
    constructor
    · intro hm0
      have hm0b : (c.m == 0) = true := beq_iff_eq.mpr hm0
      rw [if_pos hm0b] at hep
      have hZ : c.unNum * (N : ℤ) * uZ + linZ < 0 := by simpa [linZ, cZ, cgZ, cqZ, uZ] using decide_eq_true_eq.mp hep
      have hm1 : (mDen : ℚ) = 1 := by rw [hmDen_eq_orig]; simp [hm0b]
      rw [hL_eq, hm1, mul_one, mul_one]
      exact div_neg_of_neg_of_pos (by exact_mod_cast hZ) (by positivity)
    · intro hmpos
      have hm0b : (c.m == 0) = false := beq_false_of_ne (Nat.ne_of_gt hmpos)
      rw [if_neg (by simp [hm0b])] at hep
      have hδD : 0 < c.δDen := by by_contra h; simp [Nat.ne_of_gt hmpos, show c.δDen = 0 by omega] at h4
      have hδDQ : (0 : ℚ) < (c.δDen : ℚ) := by exact_mod_cast hδD
      have hZ := decide_eq_true_eq.mp hep
      have hv := vquotNum_div_eq 2 c.m c.s hmpos cNum cDen (by exact_mod_cast hcD)
      simp only [Int.cast_natCast] at hv
      have hmDen_eq : (mDen : ℚ) = (c.m : ℚ) * (c.m : ℚ) := by rw [hmDen_eq_orig]; simp [hm0b]
      have hvD_eq : (vquotDen c.m cDen : ℚ) = (N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (cDen : ℚ) := by
        unfold vquotDen; rw [hmDen_eq]; push_cast; ring
      have hsub_eq : L ((cNum : ℚ) / (cDen : ℚ)) ((cgNum : ℚ) / (cgDen : ℚ)) ((cqNum : ℚ) / (cqDen : ℚ)) -
            (c.vx : ℚ) * vquotLbQ 2 c.m c.s ((cNum : ℚ) / (cDen : ℚ)) =
          (((c.unNum : ℚ) * (N : ℚ) * (uZ : ℚ) + (linZ : ℚ) * (mDen : ℚ)) * (8 * (wY : ℚ) * (cDen : ℚ)) -
            (c.vx : ℚ) * (vquotNum 2 c.m c.s cNum cDen : ℚ) * ((cgDen : ℚ) * (cqDen : ℚ))) /
          ((N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (uZ : ℚ)) := by
        rw [hL_eq, ← hv, hvD_eq, huQ]
        field_simp [hNQ.ne', hmDenQ.ne', hcDQ.ne', hcgDQ.ne', hcqDQ.ne', hwYQ.ne']
      rw [hsub_eq]
      have hDpos : (0 : ℚ) < (N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (uZ : ℚ) := by positivity
      rw [show -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) = -((c.vx : ℚ) * (c.δNum : ℚ)) / (c.δDen : ℚ) by ring]
      rw [div_lt_div_iff₀ hDpos hδDQ]
      have hZ' : ((c.unNum * (N : ℤ) * uZ + linZ * mDen) * (8 * (wY : ℤ) * (cDen : ℤ)) -
          (c.vx : ℤ) * vquotNum 2 c.m c.s cNum cDen * ((cgDen : ℤ) * (cqDen : ℤ))) * (c.δDen : ℤ) <
          -((c.vx : ℤ) * (c.δNum : ℤ) * ((N : ℤ) * mDen * (8 * (wY : ℤ) * (cDen : ℤ)) * uZ)) := by
        rw [hmDen_eq_orig]
        simpa [linZ, cZ, cgZ, cqZ, uZ, hm0b] using hZ
      have hQ : (((c.unNum : ℚ) * (N : ℚ) * (uZ : ℚ) + (linZ : ℚ) * (mDen : ℚ)) * (8 * (wY : ℚ) * (cDen : ℚ)) -
          (c.vx : ℚ) * (vquotNum 2 c.m c.s cNum cDen : ℚ) * ((cgDen : ℚ) * (cqDen : ℚ))) * (c.δDen : ℚ) <
          -((c.vx : ℚ) * (c.δNum : ℚ) * ((N : ℚ) * (mDen : ℚ) * (8 * (wY : ℚ) * (cDen : ℚ)) * (uZ : ℚ))) := by
        exact_mod_cast hZ'
      linarith
  -- Unpack triangle checks at cLo and cHi!
  have hTri : ∀ (cNum cDen : ℕ) (hcD : 0 < cDen) (hT : checkT3_2BTri c cNum cDen = true),
      let x : ℚ := (cNum : ℚ) / (cDen : ℚ)
      11 ≤ x + 2 / (wY : ℚ) ∧
      (c.m = 0 → L x 6 2 < 0 ∧ L x (x - 5 + 2 / (wY : ℚ)) 2 < 0 ∧ L x (x - 5 + 2 / (wY : ℚ)) (x - 9 + 2 / (wY : ℚ)) < 0) ∧
      (0 < c.m →
        L x 6 2 - (c.vx : ℚ) * vquotLbQ 2 c.m c.s x < -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) ∧
        L x (x - 5 + 2 / (wY : ℚ)) 2 - (c.vx : ℚ) * vquotLbQ 2 c.m c.s x < -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) ∧
        L x (x - 5 + 2 / (wY : ℚ)) (x - 9 + 2 / (wY : ℚ)) - (c.vx : ℚ) * vquotLbQ 2 c.m c.s x < -(c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ))) := by
    intro cNum cDen hcD hT
    unfold checkT3_2BTri at hT
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hT
    rcases hT with ⟨⟨⟨⟨h11, _⟩, hV1⟩, hV2⟩, hV3⟩
    have hdW : 0 < cDen * wY := Nat.mul_pos hcD (by norm_num [wY, D])
    have hcDQ : (0 : ℚ) < (cDen : ℚ) := by exact_mod_cast hcD
    have hsub5 : 5 * (cDen * wY) ≤ cNum * wY + 2 * cDen := by omega
    have hsub9 : 9 * (cDen * wY) ≤ cNum * wY + 2 * cDen := by omega
    have h5eq : ((cNum * wY + 2 * cDen - 5 * (cDen * wY) : ℕ) : ℚ) / ((cDen * wY : ℕ) : ℚ) =
        (cNum : ℚ) / (cDen : ℚ) - 5 + 2 / (wY : ℚ) := by
      rw [Nat.cast_sub hsub5]; push_cast; field_simp [hcDQ.ne', hwYQ.ne']; ring
    have h9eq : ((cNum * wY + 2 * cDen - 9 * (cDen * wY) : ℕ) : ℚ) / ((cDen * wY : ℕ) : ℚ) =
        (cNum : ℚ) / (cDen : ℚ) - 9 + 2 / (wY : ℚ) := by
      rw [Nat.cast_sub hsub9]; push_cast; field_simp [hcDQ.ne', hwYQ.ne']; ring
    have h11Q : 11 ≤ (cNum : ℚ) / (cDen : ℚ) + 2 / (wY : ℚ) := by
      have hQ : (11 : ℚ) * ((cDen : ℚ) * (wY : ℚ)) ≤ (cNum : ℚ) * (wY : ℚ) + 2 * (cDen : ℚ) := by exact_mod_cast h11
      rw [show (cNum : ℚ) / (cDen : ℚ) + 2 / (wY : ℚ) =
          ((cNum : ℚ) * (wY : ℚ) + 2 * (cDen : ℚ)) / ((cDen : ℚ) * (wY : ℚ)) by field_simp [hcDQ.ne', hwYQ.ne']]
      rw [le_div_iff₀ (by positivity)]; linarith
    have c1 := hL_corner cNum cDen 6 1 2 1 hcD (by norm_num) (by norm_num) hV1
    have c2 := hL_corner cNum cDen _ _ 2 1 hcD hdW (by norm_num) hV2
    have c3 := hL_corner cNum cDen _ _ _ _ hcD hdW hdW hV3
    simp only [Nat.cast_ofNat, Nat.cast_one, div_one, h5eq, h9eq] at c1 c2 c3
    exact ⟨h11Q, fun hm0 => ⟨c1.1 hm0, c2.1 hm0, c3.1 hm0⟩, fun hmpos => ⟨c1.2 hmpos, c2.2 hmpos, c3.2 hmpos⟩⟩
  have hTriLo := hTri c.cLoNum c.cLoDen hcLoD hepLo
  have hTriHi := hTri c.cHiNum c.cHiDen hcHiD hepHi
  set cLoQ : ℚ := (c.cLoNum : ℚ) / (c.cLoDen : ℚ)
  set cHiQ : ℚ := (c.cHiNum : ℚ) / (c.cHiDen : ℚ)
  set t : ℚ := (cVal - cLoQ) / (cHiQ - cLoQ)
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) (sub_pos.mpr hcltQ).le
  have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hcltQ)).mpr (sub_le_sub_right hhi _)
  have hcVal_eq : cVal = (1 - t) * cLoQ + t * cHiQ := by
    have hden : cHiQ - cLoQ ≠ 0 := (sub_pos.mpr hcltQ).ne'
    dsimp only [t]; field_simp [hden]; ring
  have hL_aff : ∀ x₁ y₁ z₁ x₂ y₂ z₂ s : ℚ,
      L ((1 - s) * x₁ + s * x₂) ((1 - s) * y₁ + s * y₂) ((1 - s) * z₁ + s * z₂) =
      (1 - s) * L x₁ y₁ z₁ + s * L x₂ y₂ z₂ := by
    intro x₁ y₁ z₁ x₂ y₂ z₂ s
    have hconst : ∀ a : ℚ, a = (1 - s) * a + s * a := fun a => by ring
    have hadd : ∀ a₁ a₂ b₁ b₂ : ℚ, ((1 - s) * a₁ + s * a₂) + ((1 - s) * b₁ + s * b₂) =
        (1 - s) * (a₁ + b₁) + s * (a₂ + b₂) := fun _ _ _ _ => by ring
    have haddC : ∀ a₁ a₂ k : ℚ, ((1 - s) * a₁ + s * a₂) + k = (1 - s) * (a₁ + k) + s * (a₂ + k) :=
      fun _ _ _ => by ring
    have hlmul : ∀ k a₁ a₂ : ℚ, k * ((1 - s) * a₁ + s * a₂) = (1 - s) * (k * a₁) + s * (k * a₂) :=
      fun _ _ _ => by ring
    have hrmul : ∀ k a₁ a₂ : ℚ, ((1 - s) * a₁ + s * a₂) * k = (1 - s) * (a₁ * k) + s * (a₂ * k) :=
      fun _ _ _ => by ring
    have hdiv : ∀ k a₁ a₂ : ℚ, ((1 - s) * a₁ + s * a₂) / k = (1 - s) * (a₁ / k) + s * (a₂ / k) :=
      fun _ _ _ => by ring
    have t0 : (c.unNum : ℚ) / (mDen : ℚ) - (c.ua : ℚ) * ((A : ℚ) / (N : ℚ)) =
        (1 - s) * ((c.unNum : ℚ) / (mDen : ℚ) - (c.ua : ℚ) * ((A : ℚ) / (N : ℚ))) +
        s * ((c.unNum : ℚ) / (mDen : ℚ) - (c.ua : ℚ) * ((A : ℚ) / (N : ℚ))) := hconst _
    have t1 : ((1 - s) * z₁ + s * z₂) * (wY : ℚ) / (N : ℚ) =
        (1 - s) * (z₁ * (wY : ℚ) / (N : ℚ)) + s * (z₂ * (wY : ℚ) / (N : ℚ)) := by rw [hrmul, hdiv]
    have t2 : (((1 - s) * y₁ + s * y₂) - ((1 - s) * z₁ + s * z₂)) * (wY : ℚ) / (N : ℚ) =
        (1 - s) * ((y₁ - z₁) * (wY : ℚ) / (N : ℚ)) + s * ((y₂ - z₂) * (wY : ℚ) / (N : ℚ)) := by
      rw [show ((1 - s) * y₁ + s * y₂) - ((1 - s) * z₁ + s * z₂) = (1 - s) * (y₁ - z₁) + s * (y₂ - z₂) by ring, hrmul, hdiv]
    have t3 : (((1 - s) * x₁ + s * x₂ - 1 - ((1 - s) * y₁ + s * y₂)) * (wY : ℚ) + 1) / (N : ℚ) =
        (1 - s) * (((x₁ - 1 - y₁) * (wY : ℚ) + 1) / (N : ℚ)) + s * (((x₂ - 1 - y₂) * (wY : ℚ) + 1) / (N : ℚ)) := by
      rw [show (1 - s) * x₁ + s * x₂ - 1 - ((1 - s) * y₁ + s * y₂) = (1 - s) * (x₁ - 1 - y₁) + s * (x₂ - 1 - y₂) by ring,
        hrmul, haddC, hdiv]
    have t4 : (((1 - s) * x₁ + s * x₂ - 2 - ((1 - s) * y₁ + s * y₂) - ((1 - s) * z₁ + s * z₂)) * (wY : ℚ) + 2) / (N : ℚ) =
        (1 - s) * (((x₁ - 2 - y₁ - z₁) * (wY : ℚ) + 2) / (N : ℚ)) + s * (((x₂ - 2 - y₂ - z₂) * (wY : ℚ) + 2) / (N : ℚ)) := by
      rw [show (1 - s) * x₁ + s * x₂ - 2 - ((1 - s) * y₁ + s * y₂) - ((1 - s) * z₁ + s * z₂) =
          (1 - s) * (x₁ - 2 - y₁ - z₁) + s * (x₂ - 2 - y₂ - z₂) by ring, hrmul, haddC, hdiv]
    have t5 : ((1 - s) * z₁ + s * z₂ - 2) * (wY : ℚ) / (N : ℚ) =
        (1 - s) * ((z₁ - 2) * (wY : ℚ) / (N : ℚ)) + s * ((z₂ - 2) * (wY : ℚ) / (N : ℚ)) := by
      rw [show (1 - s) * z₁ + s * z₂ - 2 = (1 - s) * (z₁ - 2) + s * (z₂ - 2) by ring, hrmul, hdiv]
    have t6 : (((1 - s) * y₁ + s * y₂) - ((1 - s) * z₁ + s * z₂) - 4) * (wY : ℚ) / (N : ℚ) =
        (1 - s) * ((y₁ - z₁ - 4) * (wY : ℚ) / (N : ℚ)) + s * ((y₂ - z₂ - 4) * (wY : ℚ) / (N : ℚ)) := by
      rw [show ((1 - s) * y₁ + s * y₂) - ((1 - s) * z₁ + s * z₂) - 4 =
          (1 - s) * (y₁ - z₁ - 4) + s * (y₂ - z₂ - 4) by ring, hrmul, hdiv]
    have t7 : (((1 - s) * x₁ + s * x₂ - 5 - ((1 - s) * y₁ + s * y₂)) * (wY : ℚ) + 1) / (N : ℚ) =
        (1 - s) * (((x₁ - 5 - y₁) * (wY : ℚ) + 1) / (N : ℚ)) + s * (((x₂ - 5 - y₂) * (wY : ℚ) + 1) / (N : ℚ)) := by
      rw [show (1 - s) * x₁ + s * x₂ - 5 - ((1 - s) * y₁ + s * y₂) = (1 - s) * (x₁ - 5 - y₁) + s * (x₂ - 5 - y₂) by ring,
        hrmul, haddC, hdiv]
    have t8 : ((2 * ((1 - s) * x₁ + s * x₂ - 1 - ((1 - s) * y₁ + s * y₂)) + 4 * ((1 - s) * z₁ + s * z₂) - 8) * (wY : ℚ) + 2) / (N : ℚ) =
        (1 - s) * (((2 * (x₁ - 1 - y₁) + 4 * z₁ - 8) * (wY : ℚ) + 2) / (N : ℚ)) +
        s * (((2 * (x₂ - 1 - y₂) + 4 * z₂ - 8) * (wY : ℚ) + 2) / (N : ℚ)) := by
      rw [show 2 * ((1 - s) * x₁ + s * x₂ - 1 - ((1 - s) * y₁ + s * y₂)) + 4 * ((1 - s) * z₁ + s * z₂) - 8 =
          (1 - s) * (2 * (x₁ - 1 - y₁) + 4 * z₁ - 8) + s * (2 * (x₂ - 1 - y₂) + 4 * z₂ - 8) by ring,
        hrmul, haddC, hdiv]
    have t9 : (2 * ((1 - s) * x₁ + s * x₂ - 11) + 11 * ((1 - s) * z₁ + s * z₂)) * (wY : ℚ) / (N : ℚ) =
        (1 - s) * ((2 * (x₁ - 11) + 11 * z₁) * (wY : ℚ) / (N : ℚ)) +
        s * ((2 * (x₂ - 11) + 11 * z₂) * (wY : ℚ) / (N : ℚ)) := by
      rw [show 2 * ((1 - s) * x₁ + s * x₂ - 11) + 11 * ((1 - s) * z₁ + s * z₂) =
          (1 - s) * (2 * (x₁ - 11) + 11 * z₁) + s * (2 * (x₂ - 11) + 11 * z₂) by ring, hrmul, hdiv]
    have t10 : (4 * ((1 - s) * x₁ + s * x₂ - 11) + 11 * (((1 - s) * y₁ + s * y₂) - ((1 - s) * z₁ + s * z₂))) * (wY : ℚ) / (N : ℚ) =
        (1 - s) * ((4 * (x₁ - 11) + 11 * (y₁ - z₁)) * (wY : ℚ) / (N : ℚ)) +
        s * ((4 * (x₂ - 11) + 11 * (y₂ - z₂)) * (wY : ℚ) / (N : ℚ)) := by
      rw [show 4 * ((1 - s) * x₁ + s * x₂ - 11) + 11 * (((1 - s) * y₁ + s * y₂) - ((1 - s) * z₁ + s * z₂)) =
          (1 - s) * (4 * (x₁ - 11) + 11 * (y₁ - z₁)) + s * (4 * (x₂ - 11) + 11 * (y₂ - z₂)) by ring, hrmul, hdiv]
    dsimp only [L]
    conv_lhs =>
      rw [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10]
      rw [hlmul, hlmul, hlmul, hlmul, hlmul, hlmul, hlmul, hlmul, hlmul, hlmul]
      rw [hadd, hadd, hadd, hadd, hadd, hadd, hadd, hadd, hadd, hadd]
  -- Barycentric combination inside triangle `V1=(6,2), V2=(c-5+2/wY, 2), V3=(c-5+2/wY, c-9+2/wY)`!
  -- Let s := cVal - 11 + 2/wY ≥ 0:
  --   w1 = (cVal - 5 + 2/wY - cgVal) / s ≥ 0,
  --   w2 = (cgVal - cqVal - 4) / s ≥ 0,
  --   w3 = (cqVal - 2) / s ≥ 0,
  --   w1 + w2 + w3 = 1,
  --   w1 * (6, 2) + w2 * (cVal - 5 + 2/wY, 2) + w3 * (cVal - 5 + 2/wY, cVal - 9 + 2/wY) = (cgVal, cqVal)!!
  have hL_tri_bound : ∀ (B : ℚ),
      L cVal 6 2 < B → L cVal (cVal - 5 + 2 / (wY : ℚ)) 2 < B →
      L cVal (cVal - 5 + 2 / (wY : ℚ)) (cVal - 9 + 2 / (wY : ℚ)) < B →
      L cVal cgVal cqVal < B := by
    intro B hb1 hb2 hb3
    set s : ℚ := cVal - 11 + 2 / (wY : ℚ)
    have hs0 : 0 ≤ s := by dsimp [s]; linarith
    by_cases hs : s = 0
    · have hcq_eq : cqVal = 2 := by dsimp [s] at hs; linarith
      have hcg_eq : cgVal = 6 := by dsimp [s] at hs; linarith
      rwa [hcg_eq, hcq_eq]
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      set w1 : ℚ := (cVal - 5 + 2 / (wY : ℚ) - cgVal) / s
      set w2 : ℚ := (cgVal - cqVal - 4) / s
      set w3 : ℚ := (cqVal - 2) / s
      have hw1 : 0 ≤ w1 := div_nonneg (by linarith) hspos.le
      have hw2 : 0 ≤ w2 := div_nonneg (by linarith) hspos.le
      have hw3 : 0 ≤ w3 := div_nonneg (by linarith) hspos.le
      have hsum_w : w1 + w2 + w3 = 1 := by
        dsimp only [w1, w2, w3]; field_simp [hspos.ne']; dsimp only [s]; field_simp [hwYQ.ne']; ring
      have hL_bary : L cVal cgVal cqVal =
          w1 * L cVal 6 2 + w2 * L cVal (cVal - 5 + 2 / (wY : ℚ)) 2 +
          w3 * L cVal (cVal - 5 + 2 / (wY : ℚ)) (cVal - 9 + 2 / (wY : ℚ)) := by
        have hcg_id : cgVal = w1 * 6 + w2 * (cVal - 5 + 2 / (wY : ℚ)) + w3 * (cVal - 5 + 2 / (wY : ℚ)) := by
          dsimp only [w1, w2, w3]; field_simp [hspos.ne']; dsimp only [s]; field_simp [hwYQ.ne']; ring
        have hcq_id : cqVal = w1 * 2 + w2 * 2 + w3 * (cVal - 9 + 2 / (wY : ℚ)) := by
          dsimp only [w1, w2, w3]; field_simp [hspos.ne']; dsimp only [s]; field_simp [hwYQ.ne']; ring
        by_cases hw1_eq1 : w1 = 1
        · have hw2_0 : w2 = 0 := by linarith only [hw1_eq1, hw2, hw3, hsum_w]
          have hw3_0 : w3 = 0 := by linarith only [hw1_eq1, hw2, hw3, hsum_w]
          rw [hw1_eq1, hw2_0, hw3_0] at hcg_id hcq_id ⊢
          have hcg6 : cgVal = 6 := by linarith only [hcg_id]
          have hcq2 : cqVal = 2 := by linarith only [hcq_id]
          rw [hcg6, hcq2]; ring
        · have h1mw1 : 1 - w1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1_eq1)
          set u : ℚ := w3 / (1 - w1)
          have h1mu : 1 - u = w2 / (1 - w1) := by
            dsimp only [u]; field_simp [h1mw1]; linarith only [hsum_w]
          have hstep1 := hL_aff cVal (cVal - 5 + 2 / (wY : ℚ)) 2 cVal (cVal - 5 + 2 / (wY : ℚ)) (cVal - 9 + 2 / (wY : ℚ)) u
          have hstep2 := hL_aff cVal 6 2
            ((1 - u) * cVal + u * cVal)
            ((1 - u) * (cVal - 5 + 2 / (wY : ℚ)) + u * (cVal - 5 + 2 / (wY : ℚ)))
            ((1 - u) * 2 + u * (cVal - 9 + 2 / (wY : ℚ))) (1 - w1)
          rw [hstep1] at hstep2
          have hx_eq : (1 - (1 - w1)) * cVal + (1 - w1) * ((1 - u) * cVal + u * cVal) = cVal := by ring
          have hy_eq : (1 - (1 - w1)) * 6 + (1 - w1) * ((1 - u) * (cVal - 5 + 2 / (wY : ℚ)) + u * (cVal - 5 + 2 / (wY : ℚ))) = cgVal := by
            rw [h1mu, show u = w3 / (1 - w1) from rfl, hcg_id]; field_simp [h1mw1]; ring
          have hz_eq : (1 - (1 - w1)) * 2 + (1 - w1) * ((1 - u) * 2 + u * (cVal - 9 + 2 / (wY : ℚ))) = cqVal := by
            rw [h1mu, show u = w3 / (1 - w1) from rfl, hcq_id]; field_simp [h1mw1]; ring
          rw [hx_eq, hy_eq, hz_eq] at hstep2
          rw [hstep2, h1mu, show u = w3 / (1 - w1) from rfl]; field_simp [h1mw1]; ring
      rw [hL_bary]
      have h1 : w1 * L cVal 6 2 ≤ w1 * B := mul_le_mul_of_nonneg_left hb1.le hw1
      have h2 : w2 * L cVal (cVal - 5 + 2 / (wY : ℚ)) 2 ≤ w2 * B := mul_le_mul_of_nonneg_left hb2.le hw2
      have h3 : w3 * L cVal (cVal - 5 + 2 / (wY : ℚ)) (cVal - 9 + 2 / (wY : ℚ)) ≤ w3 * B := mul_le_mul_of_nonneg_left hb3.le hw3
      have hdist : (w1 + w2 + w3) * B = w1 * B + w2 * B + w3 * B := by ring
      -- At least one of w1, w2, w3 is > 0 since w1 + w2 + w3 = 1!
      have hstrict : w1 * L cVal 6 2 + w2 * L cVal (cVal - 5 + 2 / (wY : ℚ)) 2 +
          w3 * L cVal (cVal - 5 + 2 / (wY : ℚ)) (cVal - 9 + 2 / (wY : ℚ)) < (w1 + w2 + w3) * B := by
        by_cases hw1p : 0 < w1
        · have h1' := mul_lt_mul_of_pos_left hb1 hw1p; linarith only [h1', h2, h3, hdist]
        · by_cases hw2p : 0 < w2
          · have h2' := mul_lt_mul_of_pos_left hb2 hw2p; linarith only [h1, h2', h3, hdist]
          · have hw3p : 0 < w3 := by linarith only [hw1, hw2, hw1p, hw2p, hsum_w]
            have h3' := mul_lt_mul_of_pos_left hb3 hw3p; linarith only [h1, h2, h3', hdist]
      rw [hsum_w, one_mul] at hstrict; exact hstrict
  -- Interpolate each of the 3 vertices linearly in c from cLo to cHi!
  have hv1_eq : L cVal 6 2 = (1 - t) * L cLoQ 6 2 + t * L cHiQ 6 2 := by
    have h6 : (6 : ℚ) = (1 - t) * 6 + t * 6 := by ring
    have h2 : (2 : ℚ) = (1 - t) * 2 + t * 2 := by ring
    have h := hL_aff cLoQ 6 2 cHiQ 6 2 t
    rwa [← hcVal_eq, ← h6, ← h2] at h
  have hv2_eq : L cVal (cVal - 5 + 2 / (wY : ℚ)) 2 =
      (1 - t) * L cLoQ (cLoQ - 5 + 2 / (wY : ℚ)) 2 + t * L cHiQ (cHiQ - 5 + 2 / (wY : ℚ)) 2 := by
    have hy : cVal - 5 + 2 / (wY : ℚ) = (1 - t) * (cLoQ - 5 + 2 / (wY : ℚ)) + t * (cHiQ - 5 + 2 / (wY : ℚ)) := by
      rw [hcVal_eq]; ring
    have h2 : (2 : ℚ) = (1 - t) * 2 + t * 2 := by ring
    have h := hL_aff cLoQ (cLoQ - 5 + 2 / (wY : ℚ)) 2 cHiQ (cHiQ - 5 + 2 / (wY : ℚ)) 2 t
    rwa [← hcVal_eq, ← hy, ← h2] at h
  have hv3_eq : L cVal (cVal - 5 + 2 / (wY : ℚ)) (cVal - 9 + 2 / (wY : ℚ)) =
      (1 - t) * L cLoQ (cLoQ - 5 + 2 / (wY : ℚ)) (cLoQ - 9 + 2 / (wY : ℚ)) +
      t * L cHiQ (cHiQ - 5 + 2 / (wY : ℚ)) (cHiQ - 9 + 2 / (wY : ℚ)) := by
    have hy : cVal - 5 + 2 / (wY : ℚ) = (1 - t) * (cLoQ - 5 + 2 / (wY : ℚ)) + t * (cHiQ - 5 + 2 / (wY : ℚ)) := by
      rw [hcVal_eq]; ring
    have hz : cVal - 9 + 2 / (wY : ℚ) = (1 - t) * (cLoQ - 9 + 2 / (wY : ℚ)) + t * (cHiQ - 9 + 2 / (wY : ℚ)) := by
      rw [hcVal_eq]; ring
    have h := hL_aff cLoQ (cLoQ - 5 + 2 / (wY : ℚ)) (cLoQ - 9 + 2 / (wY : ℚ))
      cHiQ (cHiQ - 5 + 2 / (wY : ℚ)) (cHiQ - 9 + 2 / (wY : ℚ)) t
    rwa [← hcVal_eq, ← hy, ← hz] at h
  constructor
  · intro hm0
    have hvx0 : c.vx = 0 := by by_contra hne; simp [hm0, hne] at h3
    obtain ⟨lo1, lo2, lo3⟩ := hTriLo.2.1 hm0
    obtain ⟨hi1, hi2, hi3⟩ := hTriHi.2.1 hm0
    have hL_lt : L cVal cgVal cqVal < 0 := hL_tri_bound 0
      (by rw [hv1_eq]; exact convex_comb_lt ht0 ht1 lo1 hi1)
      (by rw [hv2_eq]; exact convex_comb_lt ht0 ht1 lo2 hi2)
      (by rw [hv3_eq]; exact convex_comb_lt ht0 ht1 lo3 hi3)
    have h0le : (0 : ℚ) ≤ L cVal cgVal cqVal := by simpa [hvx0] using hsum_all
    linarith
  · intro hmpos
    have hm0b : (c.m == 0) = false := beq_false_of_ne (Nat.ne_of_gt hmpos)
    have hvxpos : 0 < c.vx := by by_contra h; simp [Nat.ne_of_gt hmpos, show c.vx = 0 by omega] at h4
    have hvxQ : (0 : ℚ) < (c.vx : ℚ) := by exact_mod_cast hvxpos
    have hsec := vquotLbQ_ge_secant 2 c.m c.s hmpos hlo hhi hcltQ
    obtain ⟨lo1, lo2, lo3⟩ := hTriLo.2.2 hmpos
    obtain ⟨hi1, hi2, hi3⟩ := hTriHi.2.2 hmpos
    set B : ℚ := (c.vx : ℚ) * ((1 - t) * vquotLbQ 2 c.m c.s cLoQ + t * vquotLbQ 2 c.m c.s cHiQ) -
        (c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ))
    have hL_lt : L cVal cgVal cqVal < B := hL_tri_bound B
      (by rw [hv1_eq]; dsimp [B]; have hcc := convex_comb_lt ht0 ht1 lo1 hi1; linarith)
      (by rw [hv2_eq]; dsimp [B]; have hcc := convex_comb_lt ht0 ht1 lo2 hi2; linarith)
      (by rw [hv3_eq]; dsimp [B]; have hcc := convex_comb_lt ht0 ht1 lo3 hi3; linarith)
    rw [if_neg (by simp [hm0b])] at hcap
    refine ⟨?_, hcap⟩
    have h1 : (c.vx : ℚ) * ((c.δNum : ℚ) / (c.δDen : ℚ)) <
        (c.vx : ℚ) * (vquotLbQ 2 c.m c.s cVal - (∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) / (N : ℚ)) := by
      dsimp only [B] at hL_lt
      have hms := mul_le_mul_of_nonneg_left hsec hvxQ.le
      have hdist : (c.vx : ℚ) * (vquotLbQ 2 c.m c.s cVal - (∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) / (N : ℚ)) =
          (c.vx : ℚ) * vquotLbQ 2 c.m c.s cVal - (c.vx : ℚ) * ((∑ i : Idx, rankDiffQ 2 c.m c.s (k i)) / (N : ℚ)) := by ring
      linarith only [hL_lt, hms, hsum_all, hdist]
    exact lt_of_mul_lt_mul_left h1 hvxQ.le

end B6401IntSmallCerts
end ProximityPrize.SubmissionBinaryLower

