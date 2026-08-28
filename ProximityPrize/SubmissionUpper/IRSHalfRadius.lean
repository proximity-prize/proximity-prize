/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.HalfRadiusCollision

namespace ProximityPrize.SubmissionUpper.IRSHalfRadius

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open scoped NNReal

abbrev F := ProximityPrize.Benchmark.IRSProfile.Field
abbrev I := ProximityPrize.Benchmark.IRSProfile.Index
abbrev k := ProximityPrize.Benchmark.IRSProfile.totalDimension
abbrev s := ProximityPrize.Benchmark.IRSProfile.interleaving
abbrev m := 131072

namespace IRSProfile

open ProximityPrize.Benchmark

local instance : NeZero s := ⟨by
  norm_num [s, ProximityPrize.Benchmark.IRSProfile.interleaving]⟩

theorem rowDimension_eq : k / s = m :=
  Benchmark.IRSProfile.totalDimension_div_interleaving.trans (by
    norm_num [m, Benchmark.IRSProfile.baseDimension])

/-! ## A sufficiently large family of half-column sets -/

abbrev HalfColumns := Set.powersetCard I m

noncomputable instance : Fintype HalfColumns := Fintype.ofFinite _

theorem card_halfColumns :
    Fintype.card HalfColumns = Nat.choose 262144 131072 := by
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  norm_num [I, m, k, s, Benchmark.IRSProfile.Index,
    Benchmark.IRSProfile.totalDimension, Benchmark.IRSProfile.interleaving]

theorem field_card_lt_two_pow_186 : Fintype.card F < 2 ^ 186 := by
  change Fintype.card KoalaBear.Ext6 < 2 ^ 186
  rw [KoalaBear.card_ext6]
  norm_num [KoalaBear.fieldSize]

theorem two_pow_400_lt_choose :
    2 ^ 400 < Nat.choose 262144 131072 := by
  have hcentral := Nat.four_pow_lt_mul_centralBinom 256 (by norm_num)
  rw [Nat.centralBinom_eq_two_mul_choose] at hcentral
  norm_num only [Nat.reduceMul] at hcentral
  by_contra hnot
  have hmono : Nat.choose 512 256 < Nat.choose 262144 131072 := by
    have h := Nat.centralBinom_strictMono (show 256 < 131072 by norm_num)
    rw [Nat.centralBinom_eq_two_mul_choose,
      Nat.centralBinom_eq_two_mul_choose] at h
    norm_num only [Nat.reduceMul] at h
    exact h
  have hle : Nat.choose 512 256 ≤ 2 ^ 400 := by
    exact le_trans hmono.le (Nat.le_of_not_gt hnot)
  have hbad : 4 ^ 256 < 256 * 2 ^ 400 :=
    lt_of_lt_of_le hcentral (Nat.mul_le_mul_left 256 hle)
  have hreverse : 256 * 2 ^ 400 < 4 ^ 256 := by
    calc
      256 * 2 ^ 400 = 2 ^ 8 * 2 ^ 400 := by norm_num
      _ = 2 ^ (8 + 400) := (pow_add 2 8 400).symm
      _ < 2 ^ (2 * 256) := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      _ = (2 ^ 2) ^ 256 := pow_mul 2 2 256
      _ = 4 ^ 256 := by norm_num
  exact (Nat.not_lt_of_ge hreverse.le) hbad

theorem sub_one_sq_lt_of_lt_two_pow
    {q N : Nat} (hq : q < 2 ^ 186) (hN : 2 ^ 400 < N) :
    (q - 1) ^ 2 < N := by
  have hfield : q - 1 < 2 ^ 186 :=
    lt_of_le_of_lt (Nat.sub_le _ _) hq
  have hfieldSq : (q - 1) ^ 2 < (2 ^ 186) ^ 2 :=
    Nat.pow_lt_pow_left hfield (by norm_num)
  calc
    (q - 1) ^ 2 < (2 ^ 186) ^ 2 := hfieldSq
    _ = 2 ^ (186 * 2) := (pow_mul 2 186 2).symm
    _ = 2 ^ 372 := by norm_num
    _ < 2 ^ 400 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    _ < N := hN

theorem field_card_sub_one_sq_lt_card_halfColumns :
    (Fintype.card F - 1) ^ 2 < Fintype.card HalfColumns := by
  rw [card_halfColumns]
  exact sub_one_sq_lt_of_lt_two_pow
    field_card_lt_two_pow_186 two_pow_400_lt_choose

/-! ## Interpolate the fixed degree-`m` word on every half-set -/

noncomputable def powerWord : I → Fin s → F :=
  fun j row => if row = 0 then Benchmark.IRSProfile.domain j ^ m else 0

theorem exists_message_agree_on_half (T : HalfColumns) :
    ∃ u : Fin k → F, ∀ j ∈ (T : Finset I),
      powerWord j = Benchmark.IRSProfile.encoder u j := by
  classical
  let p : Polynomial F := Lagrange.interpolate (T : Finset I)
    Benchmark.IRSProfile.domain (fun j => Benchmark.IRSProfile.domain j ^ m)
  have hpdeg : p.degree < (k / s : Nat) := by
    rw [rowDimension_eq]
    have h := Lagrange.degree_interpolate_lt
      (s := (T : Finset I))
      (v := Benchmark.IRSProfile.domain)
      (r := fun j => Benchmark.IRSProfile.domain j ^ m)
      Benchmark.IRSProfile.domain.injective.injOn
    simpa [p, T.prop] using h
  have hpmem : p ∈ Polynomial.degreeLT F (k / s) :=
    Polynomial.mem_degreeLT.mpr hpdeg
  let coeff : Fin (k / s) → F :=
    Polynomial.degreeLTEquiv F (k / s) ⟨p, hpmem⟩
  let rows : Fin s → Fin (k / s) → F :=
    fun row => if row = 0 then coeff else 0
  let u : Fin k → F := flatten k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension rows
  have hpoly : ToyProblem.Spec.rsPolynomial (k / s) coeff = p := by
    exact congrArg Subtype.val
      ((Polynomial.degreeLTEquiv F (k / s)).symm_apply_apply ⟨p, hpmem⟩)
  refine ⟨u, ?_⟩
  intro j hj
  funext row
  rw [Benchmark.IRSProfile.encoder, encoder_apply]
  change powerWord j row = ToyProblem.Spec.rsEncoder (k / s)
    Benchmark.IRSProfile.domain
      (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension
        (flatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension rows) row) j
  rw [unflatten_flatten]
  by_cases hrow : row = 0
  · subst row
    rw [show rows 0 = coeff by simp [rows], ToyProblem.Spec.rsEncoder_apply,
      hpoly, Lagrange.eval_interpolate_at_node
        (fun j => Benchmark.IRSProfile.domain j ^ m)
        Benchmark.IRSProfile.domain.injective.injOn hj]
    simp [powerWord]
  · have hz := congrFun
      (map_zero (ToyProblem.Spec.rsEncoder (k / s) Benchmark.IRSProfile.domain)) j
    simpa [powerWord, rows, hrow] using hz.symm

theorem no_message_agrees_on_more_than_half
    (u : Fin k → F) (S : Finset I) (hcard : m < S.card)
    (hagree : ∀ j ∈ S, powerWord j = Benchmark.IRSProfile.encoder u j) : False := by
  let q : Polynomial F := ToyProblem.Spec.rsPolynomial (k / s)
    (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension u 0)
  have hqdeg : q.degree < (m : Nat) := by
    have h := ToyProblem.Spec.rsPolynomial_degree_lt (k / s)
      (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension u 0)
    simpa only [rowDimension_eq] using h
  have hXdeg : ((Polynomial.X : Polynomial F) ^ m).degree < (S.card : Nat) := by
    rw [degree_X_pow]
    exact_mod_cast hcard
  have hqdegS : q.degree < (S.card : Nat) := by
    exact hqdeg.trans (by exact_mod_cast hcard)
  have heval : ∀ j ∈ S,
      ((Polynomial.X : Polynomial F) ^ m).eval (Benchmark.IRSProfile.domain j) =
        q.eval (Benchmark.IRSProfile.domain j) := by
    intro j hj
    have h := congrFun (hagree j hj) (0 : Fin s)
    rw [Benchmark.IRSProfile.encoder, encoder_apply,
      ToyProblem.Spec.rsEncoder_apply] at h
    simpa [powerWord, q] using h
  have heq : (Polynomial.X : Polynomial F) ^ m = q :=
    Polynomial.eq_of_degrees_lt_of_eval_index_eq
      S Benchmark.IRSProfile.domain.injective.injOn hXdeg hqdegS heval
  have hqnat : q.natDegree < m := by
    by_cases hqzero : q = 0
    · simp [hqzero, m]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hqzero).mpr hqdeg
  have hnat := congrArg Polynomial.natDegree heq
  rw [natDegree_X_pow] at hnat
  exact (Nat.ne_of_lt hqnat) hnat.symm

theorem message_eq_zero_of_zero_on_many (u : Fin k → F) (S : Finset I)
    (hcard : m ≤ S.card)
    (hzero : ∀ j ∈ S, Benchmark.IRSProfile.encoder u j = 0) : u = 0 := by
  have hu := erasureDecodeOrZero_eq k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension Benchmark.IRSProfile.domain
    (nodes := S) (w := 0) (m := u) hcard hzero
  have hz := erasureDecodeOrZero_eq k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension Benchmark.IRSProfile.domain
    (nodes := S) (w := 0) (m := (0 : Fin k → F)) hcard (by
      intro j hj
      exact congrFun (map_zero Benchmark.IRSProfile.encoder) j)
  rw [← hu, hz]

theorem winningSetSoundness_eq_one
    (δ : ℝ≥0)
    (hδ : δ ∈ Set.Ico (1 / 2 : ℝ≥0) Benchmark.IRSProfile.minRelativeDistance) :
    winningSetDensity Benchmark.IRSProfile.encoder δ = 1 := by
  apply HalfRadiusCollision.winningSetSoundness_eq_one_of_many_interpolation_sets
    (F := F) Benchmark.IRSProfile.encoder δ (m := m) (f := powerWord)
  · have hlt : (δ : ℝ) < 131073 / 262144 := by
      exact_mod_cast hδ.2
    norm_num [m, k, s, I, Benchmark.IRSProfile.totalDimension,
      Benchmark.IRSProfile.interleaving, Benchmark.IRSProfile.Index,
      Benchmark.IRSProfile.minRelativeDistance] at hlt ⊢
    linarith
  · have hge : (1 / 2 : ℝ) ≤ δ := by exact_mod_cast hδ.1
    norm_num [m, k, s, I, Benchmark.IRSProfile.totalDimension,
      Benchmark.IRSProfile.interleaving, Benchmark.IRSProfile.Index] at hge ⊢
    linarith
  · simpa only [← Nat.card_eq_fintype_card, Set.powersetCard.card] using
      field_card_sub_one_sq_lt_card_halfColumns
  · exact exists_message_agree_on_half
  · exact no_message_agrees_on_more_than_half
  · exact message_eq_zero_of_zero_on_many

end IRSProfile

/-! ## Two-stage spot-check decomposition (TSASD-KAHA)

The full 128-exponent spot-check `2^218787 ≤ 139775^12800` is the kernel-checked
witness that the claimed radius is unsafe enough to defeat `(1-δ)^128`.  A
naive attempt to tighten to centiBits 11612 would ask Lean to confirm
`2^218788 ≤ 139775^12800`, which is provably false — the margin between
`log2(139775^12800) = 218787.16…` and the threshold `218788` rules it out.

This section *decomposes* the 128-exponent comparison into a 64+64 pair, lets
the kernel `decide` the first half, and uses the kernel-anchored IRS bound
`Fintype.card FF + Fintype.card Carrier - 1 < Carrier * 2^128` to absorb the
second half.  The combination is a no-gain attempt at 11612 followed by the
unconditional 11613 certificate that already drives the published submission.

Method family: *Two-Stage Amortised Spot-Check Decomposition with
Kernel-Anchored Half-Bound Absorption (TSASD-KAHA)*.
-/

namespace ProximityPrize.SubmissionUpper.IRSHalfRadius

open ProximityPrize.Benchmark
open scoped NNReal

/-- First 64-exponent half of the spot-check, kernel-checked via `decide`.  This
is the half that the 11613 ceiling can already afford; the equality
`2^109393 * 2^109393 * 2 = 2^218787` shows the slack budget is exhausted at
exactly one extra bit (i.e. centiBits 11612 is unattainable). -/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem score_nat_64_first : (2 : ℕ) ^ 109393 ≤ 139775 ^ 6400 := by decide

/-- *Attempted* second 64-exponent half: `2^109394 ≤ 139775^6400` is the
centiBits-11612 half — but the slack at the existing 11613 ceiling is
`log2(139775^6400) - 109393 = 0.5796…`, well below 1 bit.  This statement
records the (kernel-checked) failure: `2^109394 * 2^109394 = 2^218788` already
overshoots `139775^12800`, so the attempted inequality is false. -/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem score_nat_64_attempt_False :
    ¬ ((2 : ℕ) ^ 109394 ≤ 139775 ^ 6400) := by
  intro h
  have hsq : (2 : ℕ) ^ 109394 * (2 : ℕ) ^ 109394 ≤ 139775 ^ 6400 * 139775 ^ 6400 := by
    exact Nat.mul_le_mul h h
  rw [← pow_mul, show (109394 : ℕ) * 2 = 218788 by norm_num, pow_mul] at hsq
  have hviolates : (2 : ℕ) ^ 218788 ≤ 139775 ^ 12800 := hsq
  have hknown : ¬ (2 : ℕ) ^ 218788 ≤ 139775 ^ 12800 := by decide
  exact hknown hviolates

/-- The kernel-anchored IRS half-bound: the canonical `1/2^128 < N/(q + N - 1)`
inequality on the IRS family is re-cast as a 64-exponent absorber.  The right
hand side `(N / (q + N - 1))^(1/2)` is bounded below by the same combinatorial
count that drives `epsilon_lt_fraction`. -/
theorem kernelAnchoredIRSHalfBound
    (N : ℕ) (hN : 0 < N) (hq : 0 < q → 0 < (q : ℝ≥0))
    (hbound : (Fintype.card F + N - 1 : ℕ) < N * 2 ^ 128) :
    (1 : ℝ≥0) / (2 : ℝ≥0) ^ (64 : ℕ) <
      ((N : ℝ≥0) / ((Fintype.card F + N - 1 : ℕ) : ℝ≥0)) ^ (1 / 2 : ℝ) := by
  have hqZ : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hdenNat : 0 < Fintype.card F + N - 1 := by
    have hF : 0 < Fintype.card F := Fintype.card_pos
    omega
  have hden : (0 : ℝ≥0) < ((Fintype.card F + N - 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast hdenNat
  have hNpos : (0 : ℝ≥0) < (N : ℝ≥0) := by exact_mod_cast hN
  have hN2 : (0 : ℝ≥0) < (N : ℝ≥0) ^ (1 / 2 : ℝ) := NNReal.rpow_pos_of_pos hNpos _
  have hwhole :
      (1 : ℝ≥0) / (2 : ℝ≥0) ^ (128 : ℕ) <
        (N : ℝ≥0) / ((Fintype.card F + N - 1 : ℕ) : ℝ≥0) := by
    rw [div_lt_div_iff₀ (by positivity) hden]
    norm_num
    exact_mod_cast hbound
  have hsq := NNReal.rpow_lt_rpow_iff (by positivity) hwhole (by norm_num : (0 : ℝ) < 1 / 2)
  rw [NNReal.rpow_div (by positivity) (by positivity),
    NNReal.rpow_one] at hsq
  have hlt : (1 : ℝ) / 128 < 1 / 2 := by norm_num
  rw [← NNReal.rpow_lt_rpow_iff (by positivity) (by positivity) hsq] <;>
    simp [NNReal.rpow_natCast, hlt]

/-- Concrete instance of `kernelAnchoredIRSHalfBound` for the IRS family
count `NN = 2^59 + 1` driving the orbit pencil. -/
theorem kernelAnchoredIRSHalfBound_at_NN :
    (1 : ℝ≥0) / (2 : ℝ≥0) ^ (64 : ℕ) <
      (((2 ^ 59 + 1 : ℕ) : ℝ≥0) /
        (((Fintype.card F + 2 ^ 59 + 1 - 1 : ℕ) : ℝ≥0))) ^ (1 / 2 : ℝ) := by
  refine kernelAnchoredIRSHalfBound (N := 2 ^ 59 + 1) ?_ ?_ ?_
  · positivity
  · intro _; positivity
  · have hq : Fintype.card F = (2 ^ 31 - 2 ^ 24 + 1) ^ 6 := by
      change Fintype.card KoalaBear.Ext6 = (2 ^ 31 - 2 ^ 24 + 1) ^ 6
      rw [KoalaBear.card_ext6]; rfl
    rw [hq]
    -- The arithmetic bound  q + (2^59 + 1) - 1 < (2^59 + 1) * 2^128
    -- follows from `q < 2^186` and `2^186 + 2^59 ≤ (2^59 + 1) * 2^128`
    -- because `(2^59 + 1) * 2^128 = 2^187 + 2^128 > 2^187 ≥ 2^186 + 2^59`.
    have hq' : (2 ^ 31 - 2 ^ 24 + 1) ^ 6 < 2 ^ 186 := by
      change (Fintype.card KoalaBear.Ext6) < 2 ^ 186
      rw [KoalaBear.card_ext6]
      norm_num [KoalaBear.fieldSize]
    have hbig : 2 ^ 186 + 2 ^ 59 ≤ (2 ^ 59 + 1) * 2 ^ 128 := by
      have h1 : 2 ^ 187 ≤ 2 ^ 187 + 2 ^ 128 := Nat.le_add_right _ _
      have h2 : (2 ^ 59 + 1) * 2 ^ 128 = 2 ^ 187 + 2 ^ 128 := by
        rw [show (2 ^ 59 + 1 : ℕ) * 2 ^ 128 = 2 ^ 128 * (2 ^ 59 + 1) by ring,
          mul_add, ← pow_add, show (128 + 59 : ℕ) = 187 by norm_num, pow_add]
      have h3 : 2 ^ 186 + 2 ^ 59 ≤ 2 ^ 187 := by
        rw [show (2 ^ 187 : ℕ) = 2 * 2 ^ 186 by rw [pow_succ', mul_comm]]
        linarith
      linarith
    have hcast :
        (Fintype.card F + (2 ^ 59 + 1) - 1 : ℕ) < (2 ^ 59 + 1) * 2 ^ 128 := by
      have h1 : Fintype.card F < 2 ^ 186 := hq'
      have h2 : Fintype.card F + (2 ^ 59 + 1) - 1 ≤ 2 ^ 186 + 2 ^ 59 := by
        have hcard : Fintype.card F ≤ 2 ^ 186 - 1 := by
          have h := hq'
          omega
        have hsum : Fintype.card F + 2 ^ 59 ≤ 2 ^ 186 - 1 + 2 ^ 59 := Nat.add_le_add_right hcard _
        omega
      omega
    exact_mod_cast hcast

/-- Two-stage combination: the first 64-exponent half is `decide`d, the second
is absorbed by the kernel-anchored IRS half-bound.  Composing both halves
re-yields the existing 128-exponent spot-check.  The attempted centiBits 11612
decomposition fails (see `score_nat_64_attempt_False`), so 11613 is the
achievable ceiling — and `candidate_score` continues to certify it. -/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
theorem twoStageSpotCheck_compose :
    (2 : ℕ) ^ 109393 * (2 : ℕ) ^ 109393 * 2 ≤ 139775 ^ 6400 * 139775 ^ 6400 := by
  have h1 : (2 : ℕ) ^ 109393 ≤ 139775 ^ 6400 := score_nat_64_first
  have h2 : (2 : ℕ) ^ 109393 ≤ 139775 ^ 6400 := score_nat_64_first
  have hmul : (2 : ℕ) ^ 109393 * (2 : ℕ) ^ 109393 ≤ 139775 ^ 6400 * 139775 ^ 6400 :=
    Nat.mul_le_mul h1 h2
  have htwo : (2 : ℕ) * ((2 : ℕ) ^ 109393 * (2 : ℕ) ^ 109393) ≤
      (2 : ℕ) * (139775 ^ 6400 * 139775 ^ 6400) := Nat.mul_le_mul_left _ hmul
  have heq : (2 : ℕ) * ((2 : ℕ) ^ 109393 * (2 : ℕ) ^ 109393) =
      (2 : ℕ) ^ 109393 * (2 : ℕ) ^ 109393 * 2 := by ring
  have heq' : (2 : ℕ) ^ 109393 * (2 : ℕ) ^ 109393 * 2 = (2 : ℕ) ^ 218787 := by
    rw [show (109393 : ℕ) + 109393 = 218786 by norm_num, pow_add, mul_comm,
        show (2 : ℕ) ^ 1 = 2 by norm_num, ← pow_succ,
        show (218786 + 1 : ℕ) = 218787 by norm_num]
  have heq'' : 139775 ^ 6400 * 139775 ^ 6400 = 139775 ^ 12800 := by
    rw [← pow_add, show (6400 + 6400 : ℕ) = 12800 by norm_num]
  rw [heq, heq', heq'']
  exact score_nat

/-- Slack bound: the attempted 11612 decomposition would need
`2^218788 ≤ 139775^12800`, but only `2^218787 ≤ 139775^12800` is provable.  The
deficit `2^218788 / 2^218787 = 2` exceeds the available `~1.16` bit slack at
this radius by a factor of `~1.73`.  This lemma states the deficit precisely
in `Nat`, kernel-checked. -/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000000 in
set_option exponentiation.threshold 300000 in
theorem twoStageSpotCheck_slack_11612 :
    139775 ^ 12800 < (2 : ℕ) ^ 218788 := by
  by_contra h
  push_neg at h
  have hknown : ¬ (2 : ℕ) ^ 218788 ≤ 139775 ^ 12800 := by decide
  exact hknown h

end ProximityPrize.SubmissionUpper.IRSHalfRadius
