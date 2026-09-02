/-
Closed form for the channel count.

Provenance.  This file is adapted from the public submission of `BitWonka`
(PR #465 in `proximity-prize/proximity-prize`), which builds on an earlier
revision of this tree, so the `LocatorLowQuotient` names it refers to are
unchanged here.

`channelCount T YS S` is a `min T YS + 1` step loop, and every route stage in
the replacement grid evaluates it; a single grid row costs over a million
iterations of it, which dominates the receipt build.

Reflecting the loop (`y ↦ YS - y`) turns the summand into a function of the
index alone, and the resulting sum splits at `min S YS` into two polynomial
pieces.  This file proves the closed form, so a stage costs a constant number
of operations instead of `min T YS + 1`.

The public `LocatorLowQuotient.channelCount` definition is left untouched; the
fast form is exposed through `channelCount_eq_fast`.
-/

import ProximityPrize.SubmissionLower.LocatorNestedProjection

namespace ProximityPrize.SubmissionLower.LocatorChannelClosed

open scoped BigOperators
open ProximityPrize.SubmissionLower.LocatorLowQuotient

/-- Descending run, doubled to stay inside `ℕ`. -/
theorem two_sum_desc (C : ℕ) :
    ∀ M : ℕ, M ≤ C →
      2 * (∑ r ∈ Finset.range (M + 1), (C - r)) + M * (M + 1)
        = 2 * ((M + 1) * C) := by
  intro M
  induction M with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      rw [Finset.sum_range_succ]
      have e1 : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
      have e2 : (n + 1 + 1) * C = (n + 1) * C + C := by ring
      omega

/-- The reflected summand: at reflected index `m` the block has width
`min S m` and the outer factor is `D + 1 + m`. -/
def term (D S m : ℕ) : ℕ :=
  (min S m + 1) * (D + 1 + m) - min S m * (min S m + 1) / 2

theorem channelCount_reflect (T YS S : ℕ) (h : YS ≤ T) :
    channelCount T YS S =
      ∑ m ∈ Finset.range (YS + 1), term (T - YS) S m := by
  rw [channelCount_eq]
  rw [min_eq_right h, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hm' : m ≤ YS := by
    have := Finset.mem_range.mp hm; omega
  have hy : YS + 1 - 1 - m = YS - m := by omega
  rw [hy]
  have h1 : T - (YS - m) = T - YS + m := by omega
  have h2 : YS - (YS - m) = m := by omega
  rw [h1, h2, min_eq_right (by omega : m ≤ T - YS + m)]
  have h4 : ∀ r, T + 1 - (YS - m) - r = (T - YS + m + 1) - r := by
    intro r; omega
  simp only [h4]
  have hMle : min S m ≤ T - YS + m + 1 := by
    have : min S m ≤ m := min_le_right _ _
    omega
  have hd := two_sum_desc (T - YS + m + 1) (min S m) hMle
  obtain ⟨k, hk⟩ := Nat.even_mul_succ_self (min S m)
  have hdiv : min S m * (min S m + 1) / 2 = k := by omega
  unfold term
  rw [hdiv, show T - YS + 1 + m = T - YS + m + 1 from by omega]
  omega

/-- The doubled-and-tripled closed form of the reflected sum: subtraction free,
so it is a polynomial identity in the split variables. -/
def fastSix (D S n : ℕ) : ℕ :=
  let k := min S n
  let j := n - k
  3 * (D + 1) * (k + 1) * (k + 2) + k * (k + 1) * (k + 2)
    + 6 * (k + 1) * j * (D + 1) + 3 * (k + 1) * j * (k + j + 1)

theorem six_term (D S m : ℕ) :
    6 * term D S m
      = 6 * ((min S m + 1) * (D + 1 + m)) - 3 * (min S m * (min S m + 1)) := by
  unfold term
  obtain ⟨c, hc⟩ := Nat.even_mul_succ_self (min S m)
  have hdiv : min S m * (min S m + 1) / 2 = c := by omega
  rw [hdiv]
  have hle : c ≤ (min S m + 1) * (D + 1 + m) := by
    have h1 : min S m ≤ m := min_le_right _ _
    have h2 : (min S m + 1) * (min S m) ≤ (min S m + 1) * (D + 1 + m) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : min S m * (min S m + 1) = (min S m + 1) * (min S m) := by ring
    omega
  omega

theorem six_sum (D S : ℕ) :
    ∀ n, 6 * (∑ m ∈ Finset.range (n + 1), term D S m) = fastSix D S n := by
  intro n
  induction n with
  | zero =>
      have hs : (∑ m ∈ Finset.range (0 + 1), term D S m) = term D S 0 := by
        simp
      rw [hs]
      show 6 * term D S 0 = fastSix D S 0
      unfold term fastSix
      simp only [Nat.min_zero, Nat.zero_mul, Nat.zero_add, Nat.sub_self,
        Nat.zero_div, Nat.sub_zero, Nat.mul_zero, Nat.add_zero, Nat.one_mul]
      ring
  | succ n ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      rcases Nat.lt_or_ge n S with hlt | hge
      · have hk : min S n = n := min_eq_right (by omega)
        have hk' : min S (n + 1) = n + 1 := min_eq_right (by omega)
        have hstep : 6 * term D S (n + 1) = 3 * (n + 2) * (2 * D + n + 3) := by
          rw [six_term, hk']
          have e : 6 * ((n + 1 + 1) * (D + 1 + (n + 1)))
              = 3 * (n + 2) * (2 * D + n + 3) + 3 * ((n + 1) * (n + 1 + 1)) := by
            ring
          rw [e, Nat.add_sub_cancel]
        rw [hstep]
        simp only [fastSix, hk, hk', Nat.sub_self]
        ring
      · have hk : min S n = S := min_eq_left hge
        have hk' : min S (n + 1) = S := min_eq_left (by omega)
        obtain ⟨j, hj⟩ : ∃ j, n = S + j := ⟨n - S, by omega⟩
        subst hj
        have hstep : 6 * term D S (S + j + 1)
            = 3 * (S + 1) * (2 * D + S + 2 * j + 4) := by
          rw [six_term, hk']
          have e : 6 * ((S + 1) * (D + 1 + (S + j + 1)))
              = 3 * (S + 1) * (2 * D + S + 2 * j + 4) + 3 * (S * (S + 1)) := by
            ring
          rw [e, Nat.add_sub_cancel]
        rw [hstep]
        simp only [fastSix, hk, hk']
        have e1 : S + j - S = j := by omega
        have e2 : S + j + 1 - S = j + 1 := by omega
        rw [e1, e2]
        ring

/-- `channelCount` in closed form: constant work instead of `min T YS + 1`
loop steps. -/
def fastChannel (T YS S : ℕ) : ℕ := fastSix (T - YS) S YS / 6

theorem channelCount_eq_fast (T YS S : ℕ) (h : YS ≤ T) :
    channelCount T YS S = fastChannel T YS S := by
  have hr := channelCount_reflect T YS S h
  have hs := six_sum (T - YS) S YS
  unfold fastChannel
  rw [← hs, hr]
  omega

end ProximityPrize.SubmissionLower.LocatorChannelClosed
