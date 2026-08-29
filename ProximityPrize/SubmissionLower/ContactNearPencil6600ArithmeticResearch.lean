import ProximityPrize.Benchmark.TargetLower

/-!
# Exact arithmetic and abstract incidence algebra for the 66.00 near-pencil route

This research module contains no decoding claim.  It isolates two facts.

* Retaining the actual number `k` of identity nodes and pairing the raw
  incidence coefficient with the residual degree `w-k` is uniformly no worse
  than the zero-identity endpoint.
* If a one-layer geometric cost splits as `(w-k) * degreeCost + unitCost`,
  then raw incidence can be compressed into two fixed coefficients.  Applying
  that linear compression twice gives the exact quadratic flag expansion used
  by the proposed nested residualization route.

The polynomial residualization and the flag-preserving triangular coordinate
change are separate geometric obligations; the final ledger theorem below is
therefore only arithmetic evidence for those obligations.
-/

namespace ProximityPrize.SubmissionLower.ContactNearPencil6600ArithmeticResearch

open scoped BigOperators

/-- Cross-multiplied monotonicity of the degree-weighted raw incidence ratio.

The ratio
`(n-k) * (a-w) * (w-k) / (a-k)`
is largest at `k=0`.  The cross-multiplied form avoids division and rounding.
-/
theorem identity_degree_weight_cross_le
    (n a w k : ℕ) (hk : k ≤ w) (hwa : w < a) (han : a ≤ n) :
    (n - k) * (a - w) * (w - k) * a ≤
      n * (a - w) * w * (a - k) := by
  have hka : k ≤ a := hk.trans hwa.le
  have hkn : k ≤ n := hka.trans han
  let d := w - k
  let g := a - w
  let c := n - w
  have hdw : d ≤ w := by dsimp [d]; omega
  have haw : a = w + g := by dsimp [g]; omega
  have hnw : n = w + c := by dsimp [c]; omega
  have hak : a - k = d + g := by dsimp [d, g]; omega
  have hnk : n - k = d + c := by dsimp [d, c]; omega
  change (n - k) * g * d * a ≤ n * g * w * (a - k)
  rw [hnk, hak, haw, hnw]
  calc
    (d + c) * g * d * (w + g) ≤
        (d + c) * g * d * (w + g) +
          g * (w - d) * (w * d + g * (w + d) + c * g) := by omega
    _ = (w + c) * g * w * (d + g) := by
      let t := w - d
      have hwt : w = t + d := by
        dsimp [t]
        omega
      rw [hwt]
      have hsub : t + d - d = t := by omega
      simp only [hsub]
      ring

/-- The unit part of raw incidence is maximized at the opposite endpoint
`k=w`, giving the familiar coefficient `n-w`. -/
theorem identity_unit_weight_le
    (n a w k : ℕ) (hk : k ≤ w) (hwa : w < a) (han : a ≤ n) :
    (n - k) * (a - w) ≤ (n - w) * (a - k) := by
  have hka : k ≤ a := hk.trans hwa.le
  have hkn : k ≤ n := hka.trans han
  have hak : a - k = (w - k) + (a - w) := by omega
  have hnk : n - k = (w - k) + (n - w) := by omega
  rw [hak, hnk]
  have hgap : a - w ≤ n - w := Nat.sub_le_sub_right han w
  nlinarith [Nat.zero_le (w - k), Nat.zero_le (a - w), Nat.zero_le (n - w)]

/-- One raw-incidence layer, after splitting its geometric fiber cost into a
residual-degree part and an affine-unit part.

`U` and `V` are any cross-multiplied bounds for those two parts.  This is the
consumer-shaped algebra needed after the polynomial residual normal form.
-/
theorem stratified_incidence_linear
    (q n a w k degreeCost unitCost U V : ℕ)
    (hk : k ≤ w) (hwa : w < a)
    (hraw : q * (a - k) ≤
      (n - k) * ((w - k) * degreeCost + unitCost))
    (hdegree : (n - k) * (a - w) * (w - k) ≤ U * (a - k))
    (hunit : (n - k) * (a - w) ≤ V * (a - k)) :
    q * (a - w) ≤ U * degreeCost + V * unitCost := by
  have hak : 0 < a - k := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hak
  calc
    q * (a - w) * (a - k) = (q * (a - k)) * (a - w) := by ring
    _ ≤ ((n - k) * ((w - k) * degreeCost + unitCost)) * (a - w) :=
      Nat.mul_le_mul_right (a - w) hraw
    _ = ((n - k) * (a - w) * (w - k)) * degreeCost +
        ((n - k) * (a - w)) * unitCost := by ring
    _ ≤ (U * (a - k)) * degreeCost +
        (V * (a - k)) * unitCost :=
      Nat.add_le_add (Nat.mul_le_mul_right degreeCost hdegree)
        (Nat.mul_le_mul_right unitCost hunit)
    _ = (U * degreeCost + V * unitCost) * (a - k) := by ring

/-- Exact benchmark constants at the first 66.00 score cell. -/
def n : ℕ := 262144
def errors : ℕ := 78958
def agreements : ℕ := n - errors
def w : ℕ := 131071
def gap : ℕ := agreements - w

/-- Ceiling of `n * gap * w / agreements`: the fixed coefficient for every
degree-dependent incidence layer after identity stratification. -/
def degreeIncidence : ℕ := 9775005205

/-- Fixed coefficient for an affine unit layer. -/
def unitIncidence : ℕ := n - w

theorem parameter_values :
    agreements = 183186 ∧ gap = 52115 ∧ unitIncidence = 131073 := by
  norm_num [agreements, gap, unitIncidence, n, errors, w]

theorem degreeIncidence_is_ceiling :
    degreeIncidence * agreements - n * gap * w = 69370 ∧
      n * gap * w ≤ degreeIncidence * agreements := by
  norm_num [degreeIncidence, agreements, gap, n, errors, w]

/-- Exact specialized degree-part inequality for every possible identity
count. -/
theorem degree_part_bound (k : ℕ) (hk : k ≤ w) :
    (n - k) * gap * (w - k) ≤ degreeIncidence * (agreements - k) := by
  have hcross := identity_degree_weight_cross_le n agreements w k hk
    (by norm_num [agreements, n, errors, w])
    (by norm_num [agreements, n, errors])
  have hceil := degreeIncidence_is_ceiling.2
  have ha : 0 < agreements := by norm_num [agreements, n, errors]
  have hmul := Nat.mul_le_mul_right (agreements - k) hceil
  have htotal :
      ((n - k) * gap * (w - k)) * agreements ≤
        (degreeIncidence * (agreements - k)) * agreements := by
    calc
      ((n - k) * gap * (w - k)) * agreements =
          (n - k) * (agreements - w) * (w - k) * agreements := by
            rfl
      _ ≤ n * (agreements - w) * w * (agreements - k) := hcross
      _ ≤ (degreeIncidence * agreements) * (agreements - k) := by
        simpa only [gap] using hmul
      _ = (degreeIncidence * (agreements - k)) * agreements := by ring
  exact Nat.le_of_mul_le_mul_right htotal ha

theorem unit_part_bound (k : ℕ) (hk : k ≤ w) :
    (n - k) * gap ≤ unitIncidence * (agreements - k) := by
  simpa only [gap, unitIncidence] using
    identity_unit_weight_le n agreements w k hk
      (by norm_num [agreements, n, errors, w])
      (by norm_num [agreements, n, errors])

/-- Two nested residual-incidence layers after a bilinear geometric cost has
been expanded as `A*d₀*d₁ + B*(d₀+d₁) + C`.

The hypothesis is exactly the outer raw incidence inequality after the inner
layer has already been compressed.  The conclusion is the fixed `U,V`
quadratic consumed by the 66.00 ledger.
-/
theorem stratified_incidence_quadratic
    (q k A B C : ℕ) (hk : k ≤ w)
    (hraw : (q * gap) * (agreements - k) ≤
      (n - k) * ((w - k) *
        (A * degreeIncidence + B * unitIncidence) +
        (B * degreeIncidence + C * unitIncidence))) :
    q * gap ^ 2 ≤
      A * degreeIncidence ^ 2 +
        2 * B * degreeIncidence * unitIncidence +
        C * unitIncidence ^ 2 := by
  have hlinear := stratified_incidence_linear
    (q * gap) n agreements w k
    (A * degreeIncidence + B * unitIncidence)
    (B * degreeIncidence + C * unitIncidence)
    degreeIncidence unitIncidence hk
    (by norm_num [agreements, n, errors, w]) hraw
    (degree_part_bound k hk) (unit_part_bound k hk)
  calc
    q * gap ^ 2 = (q * gap) * gap := by ring
    _ ≤ degreeIncidence * (A * degreeIncidence + B * unitIncidence) +
        unitIncidence * (B * degreeIncidence + C * unitIncidence) := hlinear
    _ = A * degreeIncidence ^ 2 +
        2 * B * degreeIncidence * unitIncidence +
        C * unitIncidence ^ 2 := by ring

/-- The exact mixed-volume coefficients in
`MV(P, d*D+U, d'*D+U) = A*d*d' + B*(d+d') + C`
for the 66.00 flag row. -/
def mixedQuadratic : ℕ := 3425875
def mixedLinear : ℕ := 15465
def mixedUnit : ℕ := 8

/-- Exact coefficients in `MV(P, d*D+U, eZ) = zLinear*d+zUnit`. -/
def zLinear : ℕ := 1205
def zUnit : ℕ := 8

def stratifiedPrimary : ℕ :=
  mixedQuadratic * degreeIncidence ^ 2 +
    2 * mixedLinear * degreeIncidence * unitIncidence +
    mixedUnit * unitIncidence ^ 2

def stratifiedZTail : ℕ :=
  (errors + 1) * gap *
    (zLinear * degreeIncidence + zUnit * unitIncidence)

/-- The old singular branch is deliberately retained verbatim. -/
def retainedSingularContribution : ℕ := 6714916701272010710818955

def stratifiedTotalNumerator : ℕ :=
  stratifiedPrimary + stratifiedZTail + retainedSingularContribution

def gapSquared : ℕ := gap ^ 2
def ledgerCeiling : ℕ :=
  (stratifiedTotalNumerator + gapSquared - 1) / gapSquared
def alignmentBudget : ℕ := 137490364055697543

theorem stratified_primary_exact :
    stratifiedPrimary = 327344885660029958859664957 := by
  norm_num [stratifiedPrimary, mixedQuadratic, mixedLinear, mixedUnit,
    degreeIncidence, unitIncidence, n, w]

theorem stratified_z_tail_exact :
    stratifiedZTail = 48469491604406824705565 := by
  norm_num [stratifiedZTail, zLinear, zUnit, degreeIncidence, unitIncidence,
    errors, gap, agreements, n, w]

theorem stratified_total_exact :
    stratifiedTotalNumerator = 334108271852906376395189477 := by
  rw [show stratifiedTotalNumerator =
      stratifiedPrimary + stratifiedZTail + retainedSingularContribution by rfl,
    stratified_primary_exact, stratified_z_tail_exact]
  norm_num [retainedSingularContribution]

theorem gap_squared_exact : gapSquared = 2715973225 := by
  norm_num [gapSquared, gap, agreements, n, errors, w]

theorem ledger_ceiling_exact : ledgerCeiling = 123016040356180749 := by
  norm_num [ledgerCeiling, stratified_total_exact, gap_squared_exact]

theorem strict_budget : stratifiedTotalNumerator < alignmentBudget * gapSquared := by
  rw [stratified_total_exact, gap_squared_exact]
  norm_num [alignmentBudget]

theorem budget_slack : alignmentBudget - ledgerCeiling = 14474323699516794 := by
  rw [ledger_ceiling_exact]
  norm_num [alignmentBudget]

end ProximityPrize.SubmissionLower.ContactNearPencil6600ArithmeticResearch
