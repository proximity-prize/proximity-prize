import ProximityPrize.Benchmark.TargetLower

/-!
# Exact arithmetic and abstract incidence algebra for the 66.24 near-pencil route
-/

namespace ProximityPrize.SubmissionLower.ContactNearPencil6600ArithmeticResearch

open scoped BigOperators

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

def n : ℕ := 262144
def errors : ℕ := 79020
def agreements : ℕ := n - errors
def w : ℕ := 131071
def gap : ℕ := agreements - w

def degreeIncidence : ℕ := 9766681680
def unitIncidence : ℕ := n - w

theorem parameter_values :
    agreements = 183124 ∧ gap = 52053 ∧ unitIncidence = 131073 := by
  norm_num [agreements, gap, unitIncidence, n, errors, w]

theorem degreeIncidence_is_ceiling :
    degreeIncidence * agreements - n * gap * w = 181952 ∧
      n * gap * w ≤ degreeIncidence * agreements := by
  norm_num [degreeIncidence, agreements, gap, n, errors, w]

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

def mixedQuadratic : ℕ := 3740255
def mixedLinear : ℕ := 16829
def mixedUnit : ℕ := 8

def zLinear : ℕ := 1205
def zUnit : ℕ := 8

def stratifiedPrimary : ℕ :=
  mixedQuadratic * degreeIncidence ^ 2 +
    2 * mixedLinear * degreeIncidence * unitIncidence +
    mixedUnit * unitIncidence ^ 2

def stratifiedZTail : ℕ :=
  (errors + 1) * gap *
    (zLinear * degreeIncidence + zUnit * unitIncidence)

def retainedSingularContribution : ℕ := 7291985390280001108110897

def stratifiedTotalNumerator : ℕ :=
  stratifiedPrimary + stratifiedZTail + retainedSingularContribution

def gapSquared : ℕ := gap ^ 2
def ledgerCeiling : ℕ :=
  (stratifiedTotalNumerator + gapSquared - 1) / gapSquared
def alignmentBudget : ℕ := 137490364055697543

theorem stratified_primary_exact :
    stratifiedPrimary = 356775752729139448408339752 := by
  norm_num [stratifiedPrimary, mixedQuadratic, mixedLinear, mixedUnit,
    degreeIncidence, unitIncidence, n, w]

theorem stratified_z_tail_exact :
    stratifiedZTail = 48408586829955956967192 := by
  norm_num [stratifiedZTail, zLinear, zUnit, degreeIncidence, unitIncidence,
    errors, gap, agreements, n, w]

theorem stratified_total_exact :
    stratifiedTotalNumerator = 364116146706249405473417841 := by
  rw [show stratifiedTotalNumerator =
      stratifiedPrimary + stratifiedZTail + retainedSingularContribution by rfl,
    stratified_primary_exact, stratified_z_tail_exact]
  norm_num [retainedSingularContribution]

theorem gap_squared_exact : gapSquared = 2709514809 := by
  norm_num [gapSquared, gap, agreements, n, errors, w]

theorem ledger_ceiling_exact : ledgerCeiling = 134384261527854010 := by
  norm_num [ledgerCeiling, stratified_total_exact, gap_squared_exact]

theorem strict_budget : stratifiedTotalNumerator < alignmentBudget * gapSquared := by
  rw [stratified_total_exact, gap_squared_exact]
  norm_num [alignmentBudget]

theorem budget_slack : alignmentBudget - ledgerCeiling = 3106102527843533 := by
  rw [ledger_ceiling_exact]
  norm_num [alignmentBudget]

end ProximityPrize.SubmissionLower.ContactNearPencil6600ArithmeticResearch
