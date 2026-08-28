import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactNearPencil6600ArithmeticResearch

/-!
# Exact residual-incidence arithmetic for score 66.75
-/

namespace ProximityPrize.SubmissionLower.ContactNearPencil6630ArithmeticResearch

open ContactNearPencil6600ArithmeticResearch

def n : ℕ := 262144
def errors : ℕ := 79521
def agreements : ℕ := n - errors
def w : ℕ := 131071
def gap : ℕ := agreements - w

def degreeIncidence : ℕ := 9699214876
def unitIncidence : ℕ := n - w

theorem parameter_values :
    agreements = 182623 ∧ gap = 51552 ∧ unitIncidence = 131073 := by
  norm_num [agreements, gap, unitIncidence, n, errors, w]

theorem degreeIncidence_is_ceiling :
    degreeIncidence * agreements - n * gap * w = 100 ∧
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
          (n - k) * (agreements - w) * (w - k) * agreements := by rfl
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

def mixedQuadratic : ℕ := 7762407
def mixedLinear : ℕ := 32023
def mixedUnit : ℕ := 10
def zLinear : ℕ := 1642
def zUnit : ℕ := 10

def stratifiedPrimary : ℕ :=
  mixedQuadratic * degreeIncidence ^ 2 +
    2 * mixedLinear * degreeIncidence * unitIncidence +
    mixedUnit * unitIncidence ^ 2

def stratifiedZTail : ℕ :=
  (errors + 1) * gap *
    (zLinear * degreeIncidence + zUnit * unitIncidence)

def stratifiedYZTail : ℕ :=
  gap *
    (mixedLinear * degreeIncidence + mixedUnit * unitIncidence)

def regularNumerator : ℕ :=
  stratifiedPrimary + stratifiedZTail + stratifiedYZTail

def gapSquared : ℕ := gap ^ 2

theorem stratified_primary_exact :
    stratifiedPrimary = 730246728467463742016844930 := by
  norm_num [stratifiedPrimary, mixedQuadratic, mixedLinear, mixedUnit,
    degreeIncidence, unitIncidence, n, w]

theorem stratified_z_tail_exact :
    stratifiedZTail = 65289385669510254941568 := by
  norm_num [stratifiedZTail, zLinear, zUnit, degreeIncidence,
    unitIncidence, errors, gap, agreements, n, w]

theorem stratified_yz_tail_exact :
    stratifiedYZTail = 16011945997054030656 := by
  norm_num [stratifiedYZTail, mixedLinear, mixedUnit, degreeIncidence,
    unitIncidence, errors, gap, agreements, n, w]

theorem regular_numerator_exact :
    regularNumerator = 730312033865079249325817154 := by
  rw [show regularNumerator =
      stratifiedPrimary + stratifiedZTail + stratifiedYZTail by rfl,
    stratified_primary_exact, stratified_z_tail_exact,
    stratified_yz_tail_exact]

theorem gap_squared_exact : gapSquared = 2657608704 := by
  norm_num [gapSquared, gap, agreements, n, errors, w]

end ProximityPrize.SubmissionLower.ContactNearPencil6630ArithmeticResearch
