import ProximityPrize.SubmissionLower.BCHKSWeightedSecantAudit6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSCofactorOwnerLedger6400

/-!
The full quotient/root-count ledger for one repeated owner.

Writing `Q = C * R^e`, let `nu_i` be the local received-line order of `R`
at an agreement coordinate and let `r_i` be the root multiplicity left in
the specialized quotient `C_z(P_z)`.  Product order gives

`m <= r_i + e * nu_i`.

The clipped lower bound below is valid even when `e * nu_i > m`.  More
importantly, summing the untruncated inequality retains the term measuring
how many agreement coordinates lie above the baseline `a`.  At the j16
point this term is `m * (h-a)`, and it is much stronger than the coarse
consequence `total >= w + ceil(M/e)` whenever `h > a`.
-/

/-- Safe pointwise form of quotient multiplicity after clipping at `m`. -/
theorem clipped_cofactor_order_le
    (m e nu r : Nat) (hproduct : m <= r + e * nu) :
    m - min m (e * nu) <= r := by
  omega

/-- Sharp weighted mass of at most `k` cubic-profile coordinates when all
`b3` triple coordinates are mandatory: after the core, take double
coordinates first and then single coordinates. -/
def cubicTripleWeightedCardCap
    (b1 b2 b3 k : Nat) : Nat :=
  let slots := k - b3
  let doubles := min b2 slots
  3 * b3 + 2 * doubles + min b1 (slots - doubles)

theorem cubicTripleWeightedCardCap_upper
    (b1 b2 b3 k c1 c2 : Nat)
    (hc1 : c1 <= b1) (hc2 : c2 <= b2)
    (hcard : b3 + c1 + c2 <= k) :
    3 * b3 + c1 + 2 * c2 <=
      cubicTripleWeightedCardCap b1 b2 b3 k := by
  have hb3 : b3 <= k := by omega
  unfold cubicTripleWeightedCardCap
  dsimp only
  by_cases hb2 : b2 <= k - b3
  · rw [min_eq_left hb2]
    by_cases hb1 : b1 <= k - b3 - b2
    · rw [min_eq_left hb1]
      omega
    · rw [min_eq_right (by omega : k - b3 - b2 <= b1)]
      omega
  · rw [min_eq_right (by omega : k - b3 <= b2)]
    simp only [Nat.sub_self]
    omega

/-- Exact summed owner ledger.  `rootMass` is the sum of the specialized
quotient root multiplicities, `total` is the sum of the owner-factor local
orders, and `h` is the number of actual agreement coordinates being summed.

The degree hypothesis is stated without subtraction, so it remains valid at
all exponent sizes: `rootMass + e*w <= DX` is precisely the quotient-weight
budget obtained from additivity of weighted support degree. -/
theorem full_cofactor_owner_ledger
    (m e w DX M a h total rootMass : Nat)
    (hDX : DX + M = m * a)
    (hlocal : m * h <= rootMass + e * total)
    (hdegree : rootMass + e * w <= DX) :
    m * h + e * w + M <= m * a + e * total := by
  omega

/-- Clipped summed form.  Here `credit` is

`sum_i min m (e * nu_i)`.

The pointwise clipping lemma gives `m*h <= rootMass + credit`.  Unlike the
unclipped score inequality, this form does not let surplus multiplicity at a
high-order coordinate pay a quotient deficit at a different coordinate. -/
theorem full_clipped_cofactor_owner_ledger
    (m e w DX M a h credit rootMass : Nat)
    (hDX : DX + M = m * a)
    (hlocal : m * h <= rootMass + credit)
    (hdegree : rootMass + e * w <= DX) :
    m * h + e * w + M <= m * a + credit := by
  omega

/-- At exactly the baseline number of agreements, the clipped credit must
pay the complete factor weight plus the interpolation margin. -/
theorem clipped_credit_ge_factor_cost
    (m e w DX M a credit rootMass : Nat)
    (hDX : DX + M = m * a)
    (hlocal : m * a <= rootMass + credit)
    (hdegree : rootMass + e * w <= DX) :
    e * w + M <= credit := by
  have h := full_clipped_cofactor_owner_ledger
    m e w DX M a a credit rootMass hDX hlocal hdegree
  omega

/-- Difference form of the full ledger.  The familiar coarse score bound
is the special case `h=a`; every additional agreement costs another full
interpolation multiplicity `m` on the left. -/
theorem full_cofactor_owner_excess_ledger
    (m e w DX M a h total rootMass : Nat)
    (hDX : DX + M = m * a)
    (hlocal : m * h <= rootMass + e * total)
    (hdegree : rootMass + e * w <= DX)
    (ha : a <= h) (hw : w <= total) :
    m * (h - a) + M <= e * (total - w) := by
  have hmain := full_cofactor_owner_ledger
    m e w DX M a h total rootMass hDX hlocal hdegree
  have hha : h = (h - a) + a := by omega
  have htw : total = (total - w) + w := by omega
  rw [hha, htw] at hmain
  simp only [Nat.mul_add] at hmain
  omega

def cubicCofactorCounterE6400 : Nat := 17
def cubicCofactorCounterWeight6400 : Nat := 393213
def cubicCofactorCounterCard6400 : Nat := 189838
def cubicCofactorCounterMass6400 : Nat := 444313

/-- The previously recorded coarse worst cubic profile cannot satisfy the
full quotient ledger.  Its minimum owner has `189838` coordinates and mass
`444313`; at exponent seventeen the extra `4474` coordinates cost over
`6.6e9`, while the coarse score surplus pays only `868700`. -/
lemma recorded_cubic_profile_violates_full_ledger6400 :
    ¬ (bchksSixteenthDerivativeMultiplicity6400 *
          cubicCofactorCounterCard6400 +
          cubicCofactorCounterE6400 * cubicCofactorCounterWeight6400 +
          868689 <=
        bchksSixteenthDerivativeMultiplicity6400 * 185364 +
          cubicCofactorCounterE6400 * cubicCofactorCounterMass6400) := by
  norm_num [bchksSixteenthDerivativeMultiplicity6400,
    cubicCofactorCounterCard6400, cubicCofactorCounterE6400,
    cubicCofactorCounterWeight6400, cubicCofactorCounterMass6400]

/-- Exact size of the failure in the difference formulation. -/
lemma recorded_cubic_profile_full_ledger_gap6400 :
    bchksSixteenthDerivativeMultiplicity6400 * (189838 - 185364) +
        868689 - 17 * (444313 - 393213) = 6630825909 := by
  norm_num [bchksSixteenthDerivativeMultiplicity6400]

def cubicClippedTransitionExponent6400 : Nat := 494026
def cubicClippedWorstCore6400 : Nat := 22487
def cubicClippedWorstDouble6400 : Nat := 162877

/-- First clipped-transition survivor.  An owner on exactly `185364`
coordinates can use `22487` triple and `162877` double coordinates.  Its
clipped credit pays the exponent-weighted minimum cubic factor with positive
slack, while its ordinary weighted score is exactly `w+2`. -/
lemma cubic_clipped_transition_profile6400 :
    cubicClippedWorstCore6400 + cubicClippedWorstDouble6400 = 185364 ∧
      3 * cubicClippedWorstCore6400 +
          2 * cubicClippedWorstDouble6400 = 393215 ∧
      2 * cubicClippedWorstCore6400 +
          cubicClippedWorstDouble6400 <= 393213 - 131071 ∧
      cubicClippedTransitionExponent6400 * 393213 + 868689 <=
        cubicClippedWorstCore6400 *
            min bchksSixteenthDerivativeMultiplicity6400
              (3 * cubicClippedTransitionExponent6400) +
          cubicClippedWorstDouble6400 *
            min bchksSixteenthDerivativeMultiplicity6400
              (2 * cubicClippedTransitionExponent6400) := by
  norm_num [cubicClippedWorstCore6400, cubicClippedWorstDouble6400,
    cubicClippedTransitionExponent6400,
    bchksSixteenthDerivativeMultiplicity6400]

/-- The sharp minimum-weight cubic exponent endpoint of the clipped-credit
scan.  At `e=646385`, the largest triple count allowed by the derivative
excess ledger (`76778`) still pays the clipped quotient cost. -/
lemma cubic_clipped_last_exponent_fits6400 :
    646385 * 393213 + 868689 <=
      76778 * min bchksSixteenthDerivativeMultiplicity6400 (3 * 646385) +
        (185364 - 76778) *
          min bchksSixteenthDerivativeMultiplicity6400 (2 * 646385) := by
  norm_num [bchksSixteenthDerivativeMultiplicity6400]

/-- The next exponent misses even with all `76778` affordable triple
coordinates.  For larger triple counts the derivative-excess constraint
forces the factor weight upward, and in the clipped regime that only worsens
the inequality. -/
lemma cubic_clipped_next_exponent_misses6400 :
    76778 * min bchksSixteenthDerivativeMultiplicity6400 (3 * 646386) +
        (185364 - 76778) *
          min bchksSixteenthDerivativeMultiplicity6400 (2 * 646386) <
      646386 * 393213 + 868689 := by
  norm_num [bchksSixteenthDerivativeMultiplicity6400]

def cubicPostCofactorE6400 : Nat := 494026
def cubicPostCofactorB16400 : Nat := 0
def cubicPostCofactorB26400 : Nat := 239657
def cubicPostCofactorB36400 : Nat := 22487
def cubicPostCofactorT6400 : Nat := 284631
def cubicPostCofactorOwnerDouble6400 : Nat := 162877
def cubicPostCofactorOutsidePivot6400 : Nat := 76780
def cubicPostCofactorPivotBlock6400 : Nat := 86097

/-- Exact surviving cubic profile after imposing the clipped quotient ledger.
It lies at the last exponent before cubic local order starts clipping. -/
lemma cubic_postCofactor_profile_constraints6400 :
    cubicPostCofactorB16400 + cubicPostCofactorB26400 +
        cubicPostCofactorB36400 = 262144 ∧
      cubicPostCofactorB26400 + 2 * cubicPostCofactorB36400 =
        cubicPostCofactorT6400 ∧
      207720 < 262144 ∧
      17 <= cubicPostCofactorE6400 ∧
      cubicPostCofactorE6400 * 87382 > 868689 ∧
      (cubicPostCofactorE6400 - 1) * 393213 + 868689 <
        87382 + (cubicPostCofactorE6400 - 1) *
          (131071 + 87382 + cubicPostCofactorT6400) ∧
      cubicPostCofactorB36400 + cubicPostCofactorOwnerDouble6400 =
        185364 ∧
      3 * cubicPostCofactorB36400 +
          2 * cubicPostCofactorOwnerDouble6400 = 393215 ∧
      2 * cubicPostCofactorB36400 +
          cubicPostCofactorOwnerDouble6400 <= 393213 - 131071 := by
  norm_num [cubicPostCofactorB16400, cubicPostCofactorB26400,
    cubicPostCofactorB36400, cubicPostCofactorT6400,
    cubicPostCofactorE6400, cubicPostCofactorOwnerDouble6400]

/-- Weighted Cauchy remains on the wrong side after deleting the mandatory
triple core. -/
lemma cubic_postCofactor_weightedCauchy_fails6400 :
    325754 ^ 2 < 479314 * 325752 ∧
      479314 * 325752 - 325754 ^ 2 = 50021825612 := by
  norm_num

/-- The valid pivot/triple Johnson reduction also has nonpositive
denominator: pair blocks have guaranteed residual mass only `172194`, while
the sharp cardinal cap permits residual weighted common mass `217168`. -/
lemma cubic_postCofactor_pivotCauchy_fails6400 :
    172194 ^ 2 < 325754 * 217168 ∧
      325754 * 217168 - 172194 ^ 2 = 41092571036 := by
  norm_num

/-- Arithmetic of an explicit large set-system obstruction.  Take a pivot
with `162877` double coordinates and complement of size `76780`.  Every
other owner is the complement together with an `86097`-subset of the pivot.
Two distinct blocks intersect in at most `86096`, so the pair secant cap is
met exactly and the pivot triple intersection remains strictly below `k`.
There are already `2^128` distinct blocks by varying one choice in each of
128 disjoint pairs inside a fixed `85969`-set. -/
lemma cubic_postCofactor_explicit_setSystem_arithmetic6400 :
    cubicPostCofactorOutsidePivot6400 +
        cubicPostCofactorPivotBlock6400 =
      cubicPostCofactorOwnerDouble6400 ∧
      3 * cubicPostCofactorB36400 +
          2 * (cubicPostCofactorOutsidePivot6400 +
            (cubicPostCofactorPivotBlock6400 - 1)) = 393213 ∧
      cubicPostCofactorB36400 +
          (cubicPostCofactorPivotBlock6400 - 1) < 131071 ∧
      85969 + 128 = cubicPostCofactorPivotBlock6400 ∧
      85969 + 2 * 128 <= cubicPostCofactorOwnerDouble6400 ∧
      274979000000000001 < 2 ^ (128 : Nat) := by
  norm_num [cubicPostCofactorOutsidePivot6400,
    cubicPostCofactorPivotBlock6400, cubicPostCofactorOwnerDouble6400,
    cubicPostCofactorB36400]

end BCHKSCofactorOwnerLedger6400
end ProximityPrize.SubmissionLower
