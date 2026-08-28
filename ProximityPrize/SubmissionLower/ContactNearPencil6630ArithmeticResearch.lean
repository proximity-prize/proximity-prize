import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactNearPencil6600ArithmeticResearch

/-!
# Exact residual-incidence arithmetic for score 66.42

This is the numerical specialization at
`(errors,m,s,L,J) = (79194,29,8,617,40)`.  It reuses the parameter-free
stratified-incidence inequalities and records every numerator before any
ceiling is taken.
-/

namespace ProximityPrize.SubmissionLower.ContactNearPencil6630ArithmeticResearch

open ContactNearPencil6600ArithmeticResearch

def n : ℕ := 262144
def errors : ℕ := 79194
def agreements : ℕ := n - errors
def w : ℕ := 131071
def gap : ℕ := agreements - w

/-- `ceil(n * gap * w / agreements)`. -/
def degreeIncidence : ℕ := 9743291977
def unitIncidence : ℕ := n - w

theorem parameter_values :
    agreements = 182950 ∧ gap = 51879 ∧ unitIncidence = 131073 := by
  norm_num [agreements, gap, unitIncidence, n, errors, w]

theorem degreeIncidence_is_ceiling :
    degreeIncidence * agreements - n * gap * w = 167254 ∧
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

/-- Sharp flag mixed coefficients at `surfaceFlag6630 = (577,32,8)`. -/
def mixedQuadratic : ℕ := 3886947
def mixedLinear : ℕ := 18999
def mixedUnit : ℕ := 8
def zLinear : ℕ := 1104
def zUnit : ℕ := 8

def stratifiedPrimary : ℕ :=
  mixedQuadratic * degreeIncidence ^ 2 +
    2 * mixedLinear * degreeIncidence * unitIncidence +
    mixedUnit * unitIncidence ^ 2

def stratifiedZTail : ℕ :=
  (errors + 1) * gap *
    (zLinear * degreeIncidence + zUnit * unitIncidence)

/-- The new degree-zero fallback uses the same mixed coefficients as the
affine unit-YZ layer. -/
def stratifiedYZTail : ℕ :=
  (errors + 1) * gap *
    (mixedLinear * degreeIncidence + mixedUnit * unitIncidence)

def regularNumerator : ℕ :=
  stratifiedPrimary + stratifiedZTail + stratifiedYZTail

def gapSquared : ℕ := gap ^ 2

theorem stratified_primary_exact :
    stratifiedPrimary = 368994684884683298898736953 := by
  norm_num [stratifiedPrimary, mixedQuadratic, mixedLinear, mixedUnit,
    degreeIncidence, unitIncidence, n, w]

theorem stratified_z_tail_exact :
    stratifiedZTail = 44194089647070763376760 := by
  norm_num [stratifiedZTail, zLinear, zUnit, degreeIncidence,
    unitIncidence, errors, gap, agreements, n, w]

theorem stratified_yz_tail_exact :
    stratifiedYZTail = 760546587056194731539835 := by
  norm_num [stratifiedYZTail, mixedLinear, mixedUnit, degreeIncidence,
    unitIncidence, errors, gap, agreements, n, w]

theorem regular_numerator_exact :
    regularNumerator = 369799425561386564393653548 := by
  rw [show regularNumerator =
      stratifiedPrimary + stratifiedZTail + stratifiedYZTail by rfl,
    stratified_primary_exact, stratified_z_tail_exact,
    stratified_yz_tail_exact]

theorem gap_squared_exact : gapSquared = 2691430641 := by
  norm_num [gapSquared, gap, agreements, n, errors, w]

end ProximityPrize.SubmissionLower.ContactNearPencil6630ArithmeticResearch

#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6630ArithmeticResearch.degree_part_bound
#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6630ArithmeticResearch.unit_part_bound
#print axioms ProximityPrize.SubmissionLower.ContactNearPencil6630ArithmeticResearch.regular_numerator_exact
