/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Characteristic-p gate for the 256-label moment frontier

The live `1024`-fibre upper route asks whether finite-characteristic identities can make one
of the odd selector moments free.  The benchmark prime is unusually decisive here:

`p - 1 = 127 * 2^24`.

Consequently `p` is one modulo both the `256`-label group and the complete `2^18` NTT
domain.  Raising a domain root to the `p`-th power fixes it, and multiplication of a moment
index by any Frobenius iterate fixes the index modulo `256`.  Thus the Frobenius action has
`256` singleton exponent orbits; it cannot identify `-1`, `1`, and `3`.

Moreover the degree-`136` selector lies far below the characteristic.  Every Newton index
from `1` through `136` is nonzero modulo `p`, so the usual power-sum/top-coefficient
correspondence has no Lucas carry or vanished denominator in the relevant range.
Indeed `2^18 < p`, so no legal row/contact polynomial can contain an inseparable `X^p` term.

The companion exact audit `scripts/upper-characteristic-p-moment-frontier.cpp` exhausts all
signed relations of support at most eight among the three odd-moment columns on all `128`
antipodal pairs.  This file formalizes the characteristic arithmetic and the final atom-count
ledger, not that external enumeration.  It is a research gate rather than a score claim.
-/

namespace ProximityPrize.SubmissionUpper.CharacteristicMomentGate

def baseFieldCardinality : ℕ := 2 ^ 31 - 2 ^ 24 + 1

def labelOrder : ℕ := 256

def domainOrder : ℕ := 262144

def selectorDegree : ℕ := 136

def challengeThreshold : ℕ := 274980728111395088

theorem base_field_cardinality_value : baseFieldCardinality = 2130706433 := by
  norm_num [baseFieldCardinality]

theorem base_minus_one_factorization :
    baseFieldCardinality - 1 = 127 * 2 ^ 24 := by
  norm_num [baseFieldCardinality]

theorem base_eq_one_add_domain_multiple :
    baseFieldCardinality = 1 + domainOrder * 8128 := by
  norm_num [baseFieldCardinality, domainOrder]

theorem base_mod_label_order : baseFieldCardinality % labelOrder = 1 := by
  norm_num [baseFieldCardinality, labelOrder]

theorem base_mod_domain_order : baseFieldCardinality % domainOrder = 1 := by
  norm_num [baseFieldCardinality, domainOrder]

/-- No legal domain exponent reaches the characteristic, so derivative/contact coefficients in
the benchmark degree range cannot vanish merely through inseparability. -/
theorem domain_order_below_characteristic : domainOrder < baseFieldCardinality := by
  norm_num [domainOrder, baseFieldCardinality]

/-- The characteristic exponent acts trivially on every root of the full NTT domain. -/
theorem domain_root_frobenius_fixed
    {R : Type*} [Monoid R] (x : R) (hx : x ^ domainOrder = 1) :
    x ^ baseFieldCardinality = x := by
  rw [base_eq_one_add_domain_multiple, pow_add, pow_mul, hx]
  simp

/-- Every iterate of the characteristic exponent still fixes each NTT-domain root. -/
theorem domain_root_frobenius_iterate_fixed
    {R : Type*} [Monoid R] (x : R) (hx : x ^ domainOrder = 1) (iterate : ℕ) :
    x ^ baseFieldCardinality ^ iterate = x := by
  induction iterate with
  | zero => simp
  | succ iterate ih =>
      rw [pow_succ, pow_mul, ih]
      exact domain_root_frobenius_fixed x hx

/-- Multiplying a label exponent by any Frobenius iterate leaves it unchanged modulo 256. -/
theorem frobenius_moment_index_fixed (exponent iterate : ℕ) :
    (exponent * baseFieldCardinality ^ iterate) % labelOrder = exponent % labelOrder := by
  have hpow : baseFieldCardinality ^ iterate % labelOrder = 1 := by
    induction iterate with
    | zero => norm_num [labelOrder]
    | succ iterate ih =>
        rw [pow_succ, Nat.mul_mod, ih, base_mod_label_order]
        norm_num [labelOrder]
  rw [Nat.mul_mod, hpow]
  simp

/-- All Newton indices needed for a degree-136 locator are strictly below the characteristic. -/
theorem newton_index_below_characteristic
    {index : ℕ} (hpos : 1 ≤ index) (hle : index ≤ selectorDegree) :
    index < baseFieldCardinality := by
  norm_num [selectorDegree, baseFieldCardinality] at hpos hle ⊢
  omega

/-- In particular, none of the relevant Newton indices is zero modulo the characteristic. -/
theorem newton_index_mod_ne_zero
    {index : ℕ} (hpos : 1 ≤ index) (hle : index ≤ selectorDegree) :
    index % baseFieldCardinality ≠ 0 := by
  rw [Nat.mod_eq_of_lt (newton_index_below_characteristic hpos hle)]
  omega

theorem legal_domain_index_mod_ne_zero
    {index : ℕ} (hpos : 1 ≤ index) (hle : index ≤ domainOrder) :
    index % baseFieldCardinality ≠ 0 := by
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hle domain_order_below_characteristic)]
  omega

/-- Atom ledger used after the exact support-eight search.  Nine coordinates per nonempty
signature atom and at most 120 moving coordinates allow at most thirteen spanning atoms. -/
theorem affine_toggle_dimension_le_thirteen
    {dimension atoms : ℕ} (hspan : dimension ≤ atoms) (hatoms : 9 * atoms ≤ 120) :
    dimension ≤ 13 := by
  omega

theorem affine_xor_card_cap_below_threshold : 2 ^ 13 < challengeThreshold := by
  norm_num [challengeThreshold]

theorem challenge_threshold_bit_window :
    2 ^ 57 < challengeThreshold ∧ challengeThreshold < 2 ^ 58 := by
  norm_num [challengeThreshold]

/-- A one-dimensional Frobenius or Artin--Schreier chart is much too small. -/
theorem base_field_chart_below_threshold : baseFieldCardinality < challengeThreshold := by
  norm_num [baseFieldCardinality, challengeThreshold]

/-- Even granting one separate base-field chart for every projected label remains too small. -/
theorem all_label_charts_below_threshold :
    labelOrder * (baseFieldCardinality + 1) < challengeThreshold := by
  norm_num [labelOrder, baseFieldCardinality, challengeThreshold]

/-- Even a separate one-dimensional Frobenius chart at every NTT node is insufficient. -/
theorem all_domain_node_charts_below_threshold :
    domainOrder * (baseFieldCardinality + 1) < challengeThreshold := by
  norm_num [domainOrder, baseFieldCardinality, challengeThreshold]

/-- Exact number of base-field-sized charts needed merely to reach the challenge threshold. -/
theorem minimum_base_field_chart_count :
    (challengeThreshold + baseFieldCardinality - 1) / baseFieldCardinality = 129056131 := by
  norm_num [challengeThreshold, baseFieldCardinality]

end ProximityPrize.SubmissionUpper.CharacteristicMomentGate

#print axioms ProximityPrize.SubmissionUpper.CharacteristicMomentGate.domain_root_frobenius_fixed
#print axioms ProximityPrize.SubmissionUpper.CharacteristicMomentGate.frobenius_moment_index_fixed
#print axioms ProximityPrize.SubmissionUpper.CharacteristicMomentGate.newton_index_mod_ne_zero
#print axioms
  ProximityPrize.SubmissionUpper.CharacteristicMomentGate.affine_toggle_dimension_le_thirteen
#print axioms
  ProximityPrize.SubmissionUpper.CharacteristicMomentGate.all_label_charts_below_threshold
#print axioms
  ProximityPrize.SubmissionUpper.CharacteristicMomentGate.all_domain_node_charts_below_threshold
