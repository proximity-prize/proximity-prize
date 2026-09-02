/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionUpper.ExceptionalJointMomentGate

/-!
# Non-affine bounded-block product gate for the exceptional moment fibre

The affine-cube argument does not control an arbitrary nonlinear fibre.  This file treats a
strictly larger, genuinely nonlinear class: a full Cartesian product of arbitrary local
codebooks on disjoint endpoint blocks.  A local codebook need not be affine, linear, or even
have prime-power cardinality.

Two distinct records in one fifteen-moment/product fibre differ on at least seventeen selected
and seventeen unselected endpoints.  Consequently each local codebook is a binary code of
minimum Hamming distance 34.  If it has `q` words on a block of `s` endpoints, the Plotkin
double count gives

`68 * q * (q - 1) <= s * q * q`.

For `s <= 67`, this implies `(68 - s) * q <= 68`.  An exact finite check of the resulting 68
integer cases gives the convenient multiplicative potential `q^9 <= 2^s`.  Multiplying this
potential over disjoint blocks of total support at most 510 shows that the whole nonlinear
Cartesian product has size strictly below the challenge threshold.

Thus a threshold-sized exceptional fibre cannot decompose into independent interaction
components of at most 67 endpoints.  Any surviving nonlinear concentration must contain a
coupled component on at least 68 endpoints.  The companion deterministic audit also computes
the sharper exact product cap `13,445,977,636,864`.

The formal theorem starts at the standard Plotkin energy inequality.  The coordinate lemma
below proves the only analytic input to that inequality; summing it over coordinates and using
minimum distance 34 yields the displayed hypothesis.  This is a scoped structural gate, not a
score claim.
-/

namespace ProximityPrize.SubmissionUpper.NonAffineBlockProductGate

open ProximityPrize.SubmissionUpper.ExceptionalJointMomentGate

def endpointPool : ℕ := 510
def minimumTradeSide : ℕ := 17
def minimumHammingDistance : ℕ := 34
def twiceMinimumHammingDistance : ℕ := 68
def maximumLocalSupport : ℕ := 67
def potentialExponent : ℕ := 9
def challengeThreshold : ℕ := 274980728111395088
def exactDynamicProductCap : ℕ := 13445977636864

/-! ## From the moment/product key to Hamming separation -/

variable {F : Type*} [Field F]

/-- The coefficient/product rigidity in `ExceptionalJointMomentGate` supplies both halves of
the minimum-distance statement used by the Plotkin count. -/
theorem nontrivial_trade_support_at_least_thirty_four
    (A B : Multiset F)
    (hcard : A.card = B.card)
    (htop : ∀ k, 1 ≤ k → k ≤ 15 → (locator A).coeff k = (locator B).coeff k)
    (hprod : A.prod = B.prod) (hne : A ≠ B) :
    minimumHammingDistance ≤ A.card + B.card := by
  have hA := nontrivial_trade_side_at_least_seventeen A B hcard htop hprod hne
  have hB : minimumTradeSide ≤ B.card := by
    simpa [minimumTradeSide] using hcard ▸ hA
  norm_num [minimumTradeSide, minimumHammingDistance] at hA hB ⊢
  omega

/-! ## Plotkin energy and the local ninth-power potential -/

/-- At one binary coordinate, if `a` of the `q` codewords contain that coordinate, then the
number `a * (q-a)` of separated unordered pairs is at most `q^2 / 4`. -/
theorem one_coordinate_plotkin_bound (q a : ℕ) (ha : a ≤ q) :
    4 * a * (q - a) ≤ q * q := by
  have hsplit : a + (q - a) = q := Nat.add_sub_of_le ha
  calc
    4 * a * (q - a) ≤ (a + (q - a)) ^ 2 := four_mul_le_sq_add a (q - a)
    _ = q * q := by rw [hsplit, pow_two]

/-- Rearrangement of the Plotkin energy inequality below the binary Plotkin boundary 68. -/
theorem plotkin_rearrangement (support words : ℕ)
    (hsupport : support ≤ maximumLocalSupport) (hwords : 1 ≤ words)
    (henergy : twiceMinimumHammingDistance * words * (words - 1) ≤
      support * words * words) :
    (twiceMinimumHammingDistance - support) * words ≤
      twiceMinimumHammingDistance := by
  have hfactor :
      words * (twiceMinimumHammingDistance * (words - 1)) ≤
        words * (support * words) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using henergy
  have hcancel :
      twiceMinimumHammingDistance * (words - 1) ≤ support * words :=
    Nat.le_of_mul_le_mul_left hfactor (by omega)
  have hwordSplit : words = (words - 1) + 1 := by omega
  have hsupportSplit :
      twiceMinimumHammingDistance =
        (twiceMinimumHammingDistance - support) + support := by
    norm_num [twiceMinimumHammingDistance, maximumLocalSupport] at hsupport ⊢
    omega
  have hstep :
      (twiceMinimumHammingDistance - support) * (words - 1) ≤ support := by
    apply Nat.le_of_add_le_add_left (a := support * (words - 1))
    calc
      support * (words - 1) +
          (twiceMinimumHammingDistance - support) * (words - 1) =
          twiceMinimumHammingDistance * (words - 1) := by
        rw [← add_mul, add_comm support, ← hsupportSplit]
      _ ≤ support * words := hcancel
      _ = support * (words - 1) + support := by
        calc
          support * words = support * ((words - 1) + 1) :=
            congrArg (fun value ↦ support * value) hwordSplit
          _ = support * (words - 1) + support := by simp [mul_add]
  calc
    (twiceMinimumHammingDistance - support) * words =
        (twiceMinimumHammingDistance - support) * (words - 1) +
          (twiceMinimumHammingDistance - support) := by
      calc
        (twiceMinimumHammingDistance - support) * words =
            (twiceMinimumHammingDistance - support) * ((words - 1) + 1) :=
          congrArg (fun value ↦ (twiceMinimumHammingDistance - support) * value)
            hwordSplit
        _ = (twiceMinimumHammingDistance - support) * (words - 1) +
            (twiceMinimumHammingDistance - support) := by simp [mul_add]
    _ ≤ support + (twiceMinimumHammingDistance - support) :=
      Nat.add_le_add_right hstep _
    _ = twiceMinimumHammingDistance := by omega

def localPlotkinCap (support : ℕ) : ℕ :=
  twiceMinimumHammingDistance / (twiceMinimumHammingDistance - support)

theorem words_le_local_plotkin_cap (support words : ℕ)
    (hsupport : support ≤ maximumLocalSupport) (hwords : 1 ≤ words)
    (henergy : twiceMinimumHammingDistance * words * (words - 1) ≤
      support * words * words) :
    words ≤ localPlotkinCap support := by
  have hdenom : 0 < twiceMinimumHammingDistance - support := by
    norm_num [twiceMinimumHammingDistance, maximumLocalSupport] at hsupport ⊢
    omega
  apply (Nat.le_div_iff_mul_le hdenom).2
  rw [Nat.mul_comm]
  exact plotkin_rearrangement support words hsupport hwords henergy

/-- Exact 68-case certificate for the local multiplicative potential. -/
theorem local_plotkin_cap_ninth_power (support : ℕ)
    (hsupport : support ≤ maximumLocalSupport) :
    localPlotkinCap support ^ potentialExponent ≤ 2 ^ support := by
  norm_num [maximumLocalSupport] at hsupport
  interval_cases support <;>
    norm_num [localPlotkinCap, twiceMinimumHammingDistance, potentialExponent]

/-- Every local codebook satisfying the distance-34 Plotkin energy inequality pays at least
nine support bits per logarithmic codebook bit. -/
theorem local_codebook_ninth_power_le (support words : ℕ)
    (hsupport : support ≤ maximumLocalSupport)
    (henergy : twiceMinimumHammingDistance * words * (words - 1) ≤
      support * words * words) :
    words ^ potentialExponent ≤ 2 ^ support := by
  by_cases hzero : words = 0
  · norm_num [hzero, potentialExponent]
  have hwords : 1 ≤ words := Nat.one_le_iff_ne_zero.mpr hzero
  calc
    words ^ potentialExponent ≤ localPlotkinCap support ^ potentialExponent :=
      Nat.pow_le_pow_left
        (words_le_local_plotkin_cap support words hsupport hwords henergy) _
    _ ≤ 2 ^ support := local_plotkin_cap_ninth_power support hsupport

/-! ## Multiplication over arbitrary nonlinear local codebooks -/

/-- A list entry is `(number of local alternatives, endpoint support)`. -/
abbrev Block := ℕ × ℕ

theorem product_ninth_power_le_support_power
    (blocks : List Block)
    (hlocal : ∀ block ∈ blocks,
      block.1 ^ potentialExponent ≤ 2 ^ block.2) :
    (blocks.map Prod.fst).prod ^ potentialExponent ≤
      2 ^ (blocks.map Prod.snd).sum := by
  induction blocks with
  | nil => simp
  | cons block blocks ih =>
      have hhead := hlocal block (by simp)
      have htail : ∀ item ∈ blocks,
          item.1 ^ potentialExponent ≤ 2 ^ item.2 := by
        intro item hitem
        exact hlocal item (by simp [hitem])
      have hind := ih htail
      simpa [mul_pow, pow_add] using Nat.mul_le_mul hhead hind

/-- Any full Cartesian product of arbitrary local distance-34 codebooks on disjoint blocks of
size at most 67 is below the benchmark challenge threshold. -/
theorem bounded_block_nonlinear_product_below_threshold
    (blocks : List Block)
    (hsupport : (blocks.map Prod.snd).sum ≤ endpointPool)
    (hlocalsupport : ∀ block ∈ blocks, block.2 ≤ maximumLocalSupport)
    (henergy : ∀ block ∈ blocks,
      twiceMinimumHammingDistance * block.1 * (block.1 - 1) ≤
        block.2 * block.1 * block.1) :
    (blocks.map Prod.fst).prod < challengeThreshold := by
  have hlocal : ∀ block ∈ blocks,
      block.1 ^ potentialExponent ≤ 2 ^ block.2 := by
    intro block hblock
    exact local_codebook_ninth_power_le block.2 block.1
      (hlocalsupport block hblock) (henergy block hblock)
  have hproduct := product_ninth_power_le_support_power blocks hlocal
  have hpool :
      (blocks.map Prod.fst).prod ^ potentialExponent ≤ 2 ^ endpointPool :=
    hproduct.trans (Nat.pow_le_pow_right (by norm_num) hsupport)
  by_contra hnot
  have hthreshold : challengeThreshold ≤ (blocks.map Prod.fst).prod := by omega
  have hthresholdPower :
      challengeThreshold ^ potentialExponent ≤
        (blocks.map Prod.fst).prod ^ potentialExponent :=
    Nat.pow_le_pow_left hthreshold _
  have himpossible : challengeThreshold ^ potentialExponent ≤ 2 ^ endpointPool :=
    hthresholdPower.trans hpool
  have hbase : 2 ^ 57 < challengeThreshold := by
    norm_num [challengeThreshold]
  have hraised : (2 ^ 57) ^ potentialExponent <
      challengeThreshold ^ potentialExponent :=
    Nat.pow_lt_pow_left hbase (by norm_num [potentialExponent])
  have hexponents : 2 ^ endpointPool < (2 ^ 57) ^ potentialExponent := by
    calc
      2 ^ endpointPool < 2 ^ (57 * potentialExponent) :=
        Nat.pow_lt_pow_right (by norm_num)
          (by norm_num [endpointPool, potentialExponent])
      _ = (2 ^ 57) ^ potentialExponent := by rw [pow_mul]
  have hstrict : 2 ^ endpointPool < challengeThreshold ^ potentialExponent :=
    hexponents.trans hraised
  omega

/-! ## Exact numerical receipts -/

theorem coarse_potential_cap_below_threshold :
    2 ^ 56 < challengeThreshold := by
  norm_num [challengeThreshold]

theorem exact_dynamic_product_cap_below_threshold :
    exactDynamicProductCap < challengeThreshold := by
  norm_num [exactDynamicProductCap, challengeThreshold]

theorem exact_dynamic_product_cap_factorization :
    exactDynamicProductCap = 2 * 68 ^ 7 := by
  norm_num [exactDynamicProductCap]

end ProximityPrize.SubmissionUpper.NonAffineBlockProductGate

open ProximityPrize.SubmissionUpper.NonAffineBlockProductGate

#print axioms nontrivial_trade_support_at_least_thirty_four
#print axioms one_coordinate_plotkin_bound
#print axioms local_codebook_ninth_power_le
#print axioms bounded_block_nonlinear_product_below_threshold
#print axioms exact_dynamic_product_cap_below_threshold
