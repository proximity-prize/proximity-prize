import ProximityPrize.SubmissionLower.BCHKSDynamicCoreSelector6400
import ProximityPrize.SubmissionLower.BCHKSRaisedNumeratorEndpoint6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSDynamicCoreArithmetic6400

open BCHKSHybridHighDegreeAudit6400
open BCHKSRaisedNumeratorEndpoint6400
open scoped BigOperators

/-!
Exact arithmetic for two ways of finishing a dynamically selected common
core.  Nothing in this file asserts that either algebraic selector has been
assembled end to end; the semantic interfaces are in
`BCHKSDynamicCoreSelector6400`.

The first endpoint uses two Hensel passes on the same owner fibre and then a
cubic quotient-incidence cap.  The second constructs a fresh GS/universal
instance for the quotient received word.  The latter really is a nested
factor selection, so its complete threshold is charged once for every pair
in the first selector.
-/

def dynamicRootCap6400 : Nat := 131071
def dynamicAmbientOffset6400 : Nat := 131073
def dynamicAgreementOffset6400 : Nat := 54293
def dynamicLineCap6400 : Nat := 76780

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

def dynamicStageUnit (source remainder : Nat) : Nat :=
  ceilDiv
    ((dynamicAmbientOffset6400 + remainder) *
      (2 * (2 * source - 1)))
    (dynamicAgreementOffset6400 + remainder)

def dynamicCubicGap (t : Nat) : Nat :=
  (dynamicAgreementOffset6400 + t) ^ 3 -
    t * (dynamicAmbientOffset6400 + t) ^ 2

def dynamicCubicOwnerCap (t : Nat) : Nat :=
  ((dynamicAmbientOffset6400 + t) ^ 2 *
      dynamicAgreementOffset6400 * (dynamicLineCap6400 + 1)) /
    dynamicCubicGap t

def dynamicTwoStageUnit (source middle final : Nat) : Nat :=
  max (dynamicStageUnit source middle)
    (dynamicStageUnit middle final)

/-- Conservative two-stage ledger.  It retains the old `(errors+1)` pair
charge in addition to the cubic owner cap; this is slightly larger than the
minimal `max`-threshold ledger. -/
def dynamicTwoStageTotal (d source middle final : Nat) : Nat :=
  (dynamicTwoStageUnit source middle final + 2) * d *
      bchksHybridZMass6400 +
    dynamicCubicOwnerCap final * bchksHybridYMass6400 +
    bchksHybridPairCardCover6400 + bchksHybridQBadCover6400

lemma dynamic_twoStage_fullCodim_degree205_exact6400 :
    dynamicStageUnit 131071 94924 = 794053 /\
      dynamicStageUnit 94924 16064 = 794051 /\
      dynamicTwoStageUnit 131071 94924 16064 = 794053 /\
      dynamicCubicGap 16064 = 500406492077 /\
      dynamicCubicOwnerCap 16064 = 180350961 /\
      dynamicTwoStageTotal 205 131071 94924 16064 =
        274948840752453522 /\
      dynamicTwoStageTotal 205 131071 94924 16064 <
        bchksResidualNumerator6400 /\
      bchksResidualNumerator6400 -
          dynamicTwoStageTotal 205 131071 94924 16064 =
        31859247546478 := by
  norm_num [dynamicStageUnit, dynamicTwoStageUnit,
    dynamicCubicGap, dynamicCubicOwnerCap, dynamicTwoStageTotal,
    dynamicRootCap6400, dynamicAmbientOffset6400,
    dynamicAgreementOffset6400, dynamicLineCap6400, ceilDiv,
    bchksHybridZMass6400, bchksHybridYMass6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400,
    bchksResidualNumerator6400]

theorem dynamic_twoStage_fullCodim_fits_of_degree_le2056400
    (d : Nat) (hd : d <= 205) :
    dynamicTwoStageTotal d 131071 94924 16064 <
      bchksResidualNumerator6400 := by
  calc
    dynamicTwoStageTotal d 131071 94924 16064 <=
        dynamicTwoStageTotal 205 131071 94924 16064 := by
      unfold dynamicTwoStageTotal
      gcongr
    _ < bchksResidualNumerator6400 :=
      dynamic_twoStage_fullCodim_degree205_exact6400.2.2.2.2.2.2.1

/-! ## Fresh quotient GS/universal instance at `q = 20230`

After the first dynamic core has size `q`, the quotient instance has

* length `n' = 262144-q`,
* degree cap `s = 131071-q`, and
* agreements `a' = 185364-q`.

The displayed small interpolation template has strictly more variables than
constraints.  Its universal selector threshold is then paid for each pair of
the first selector. -/

def freshCoreSize6400 : Nat := 20230
def freshQuotientN6400 : Nat := 241914
def freshQuotientK6400 : Nat := 110841
def freshQuotientA6400 : Nat := 165134
def freshMultiplicity6400 : Nat := 28
def freshXCap6400 : Nat := 4623752
def freshYCap6400 : Nat := 42
def freshZCap6400 : Nat := 836
def freshFactorMass6400 : Nat := freshYCap6400 - 1
def freshFactorZMass6400 : Nat := freshZCap6400 - 1

def freshVarCount6400 : Nat :=
  ∑ j ∈ Finset.range freshYCap6400,
    (freshXCap6400 - freshQuotientK6400 * j) *
      (freshZCap6400 - j)

def freshConstraintCount6400 : Nat :=
  freshQuotientN6400 *
    ∑ t ∈ Finset.range freshMultiplicity6400,
      (freshMultiplicity6400 - t) * (freshZCap6400 - t)

def freshUniversalRawResultant6400 : Nat :=
  2 * (2 * freshQuotientK6400 - 1) *
    freshFactorMass6400 * freshFactorZMass6400

def freshUniversalFusedResultant6400 : Nat :=
  ceilDiv
    ((freshQuotientN6400 - freshQuotientK6400) *
      freshUniversalRawResultant6400)
    (freshQuotientA6400 - freshQuotientK6400)

def freshUniversalThreshold6400 : Nat :=
  freshUniversalFusedResultant6400 +
    (dynamicLineCap6400 + 1) * freshFactorMass6400 +
    freshFactorZMass6400

def freshFirstStageUnit6400 : Nat :=
  ceilDiv
    (freshQuotientN6400 * (2 * (2 * dynamicRootCap6400 - 1)))
    freshQuotientA6400

/-- The `+1` is the strict owner threshold required for each first-stage
pair.  The two degree-`d` outer bad sets are the `+2` in the first factor. -/
def freshNestedTotal6400 (d : Nat) : Nat :=
  (freshFirstStageUnit6400 + 2) * d * bchksHybridZMass6400 +
    (freshUniversalThreshold6400 + 1) * bchksHybridYMass6400 +
    bchksHybridQBadCover6400

lemma freshQuotient_parameters_exact6400 :
    freshQuotientN6400 + freshCoreSize6400 = 262144 /\
      freshQuotientK6400 + freshCoreSize6400 = 131071 /\
      freshQuotientA6400 + freshCoreSize6400 = 185364 /\
      freshXCap6400 = freshMultiplicity6400 * freshQuotientA6400 /\
      freshQuotientK6400 * (freshYCap6400 - 1) < freshXCap6400 /\
      freshMultiplicity6400 <= freshZCap6400 /\
      freshYCap6400 <= freshZCap6400 := by
  norm_num [freshQuotientN6400, freshCoreSize6400,
    freshQuotientK6400, freshQuotientA6400,
    freshXCap6400, freshMultiplicity6400, freshYCap6400,
    freshZCap6400]

lemma freshQuotient_dimension_exact6400 :
    freshVarCount6400 = 81225564777 /\
      freshConstraintCount6400 = 81225528468 /\
      freshConstraintCount6400 < freshVarCount6400 /\
      freshVarCount6400 - freshConstraintCount6400 = 36309 := by
  norm_num [freshVarCount6400, freshConstraintCount6400,
    freshYCap6400, freshXCap6400, freshQuotientK6400,
    freshZCap6400, freshQuotientN6400, freshMultiplicity6400,
    Finset.sum_range_succ]

lemma freshQuotient_universalCapacity_exact6400 :
    freshFactorMass6400 = 41 /\
      freshFactorZMass6400 = 835 /\
      freshUniversalFusedResultant6400 = 36643605576 /\
      (freshQuotientN6400 - freshQuotientK6400) *
          freshUniversalRawResultant6400 <=
        (freshQuotientA6400 - freshQuotientK6400) *
          freshUniversalFusedResultant6400 /\
      freshUniversalThreshold6400 = 36646754432 /\
      freshFirstStageUnit6400 = 768050 := by
  norm_num [freshFactorMass6400, freshFactorZMass6400,
    freshUniversalFusedResultant6400,
    freshUniversalRawResultant6400, freshUniversalThreshold6400,
    freshFirstStageUnit6400, freshQuotientN6400,
    freshQuotientK6400, freshQuotientA6400,
    freshYCap6400, freshZCap6400, dynamicLineCap6400,
    dynamicRootCap6400, ceilDiv]

lemma freshNested_degree209_exact6400 :
    freshNestedTotal6400 209 = 274219753325375763 /\
      freshNestedTotal6400 209 < bchksResidualNumerator6400 /\
      bchksResidualNumerator6400 - freshNestedTotal6400 209 =
        760946674624237 /\
      freshNestedTotal6400 210 = 275516974280802019 /\
      bchksResidualNumerator6400 < freshNestedTotal6400 210 /\
      freshNestedTotal6400 210 - bchksResidualNumerator6400 =
        536274280802019 := by
  norm_num [freshNestedTotal6400, freshFirstStageUnit6400,
    freshUniversalThreshold6400, freshUniversalFusedResultant6400,
    freshUniversalRawResultant6400, freshFactorMass6400,
    freshFactorZMass6400, freshQuotientN6400,
    freshQuotientK6400, freshQuotientA6400,
    freshYCap6400, freshZCap6400, dynamicLineCap6400,
    dynamicRootCap6400, ceilDiv, bchksHybridZMass6400,
    bchksHybridYMass6400, bchksHybridQBadCover6400,
    bchksResidualNumerator6400]

theorem freshNested_fits_of_degree_le2096400
    (d : Nat) (hd : d <= 209) :
    freshNestedTotal6400 d < bchksResidualNumerator6400 := by
  calc
    freshNestedTotal6400 d <= freshNestedTotal6400 209 := by
      unfold freshNestedTotal6400
      gcongr
    _ < bchksResidualNumerator6400 :=
      freshNested_degree209_exact6400.2.1

/-! The concrete normalized-factor cover pays one additional global term
`2 * 835 * 41` for outer leading/separability bad fibres.  The earlier rough
threshold omitted it.  The correction is tiny relative to the d=209
headroom, but it is recorded here so the compiled chain and arithmetic ledger
match exactly. -/

def freshOuterBadCap6400 : Nat :=
  2 * freshFactorZMass6400 * freshFactorMass6400

def freshUniversalThresholdCorrected6400 : Nat :=
  freshUniversalThreshold6400 + freshOuterBadCap6400

def freshNestedTotalCorrected6400 (d : Nat) : Nat :=
  (freshFirstStageUnit6400 + 2) * d * bchksHybridZMass6400 +
    (freshUniversalThresholdCorrected6400 + 1) * bchksHybridYMass6400 +
    bchksHybridQBadCover6400

lemma freshQuotient_corrected_selector_exact6400 :
    freshOuterBadCap6400 = 68470 ∧
      freshUniversalThresholdCorrected6400 = 36646822902 ∧
      freshNestedTotalCorrected6400 209 = 274219759118417053 ∧
      freshNestedTotalCorrected6400 209 < bchksResidualNumerator6400 ∧
      bchksResidualNumerator6400 -
          freshNestedTotalCorrected6400 209 = 760940881582947 ∧
      freshNestedTotalCorrected6400 210 = 275516980073843309 ∧
      bchksResidualNumerator6400 <
          freshNestedTotalCorrected6400 210 ∧
      freshNestedTotalCorrected6400 210 - bchksResidualNumerator6400 =
        536280073843309 := by
  norm_num [freshOuterBadCap6400, freshUniversalThresholdCorrected6400,
    freshNestedTotalCorrected6400, freshUniversalThreshold6400,
    freshUniversalFusedResultant6400, freshUniversalRawResultant6400,
    freshFirstStageUnit6400, freshFactorMass6400,
    freshFactorZMass6400, freshQuotientN6400, freshQuotientK6400,
    freshQuotientA6400, freshYCap6400, freshZCap6400,
    dynamicLineCap6400, dynamicRootCap6400, ceilDiv,
    bchksHybridZMass6400, bchksHybridYMass6400,
    bchksHybridQBadCover6400, bchksResidualNumerator6400]

theorem freshNested_corrected_fits_of_degree_le2096400
    (d : Nat) (hd : d ≤ 209) :
    freshNestedTotalCorrected6400 d < bchksResidualNumerator6400 := by
  calc
    freshNestedTotalCorrected6400 d ≤
        freshNestedTotalCorrected6400 209 := by
      unfold freshNestedTotalCorrected6400
      gcongr
    _ < bchksResidualNumerator6400 :=
      freshQuotient_corrected_selector_exact6400.2.2.2.1

/-! ## Ideal repeated-stage ceiling

Suppose every later dynamic-core pass can reuse the already selected owner
fibre, so stage capacities combine by `max` rather than by addition or
multiplication.  Infinitesimal one-coordinate extraction is then the most
optimistic possible schedule.  Its unavoidable first edge is `741448`.
Even granting a free arbitrarily deep recursion after that edge, plus the
smallest cubic endpoint (`t=0`), degree `219` fits and degree `220` does not.
-/

def dynamicIdealFirstUnit6400 : Nat :=
  dynamicStageUnit 131071 131070

def dynamicIdealRecursiveTotal6400 (d : Nat) : Nat :=
  (dynamicIdealFirstUnit6400 + 2) * d * bchksHybridZMass6400 +
    dynamicCubicOwnerCap 0 * bchksHybridYMass6400 +
    bchksHybridPairCardCover6400 + bchksHybridQBadCover6400

lemma dynamic_ideal_firstUnit_exact6400 :
    dynamicIdealFirstUnit6400 = 741448 := by
  norm_num [dynamicIdealFirstUnit6400, dynamicStageUnit, ceilDiv,
    dynamicAmbientOffset6400, dynamicAgreementOffset6400]

/-- Any genuine first reduction from the full root cap costs at least the
one-coordinate edge.  Thus varying the first `q` cannot beat `741448`. -/
theorem dynamic_firstStageUnit_ge_ideal6400
    (remainder : Nat) (hrem : remainder < 131071) :
    dynamicIdealFirstUnit6400 ≤ dynamicStageUnit 131071 remainder := by
  rw [dynamic_ideal_firstUnit_exact6400]
  unfold dynamicStageUnit ceilDiv
  norm_num [dynamicAmbientOffset6400, dynamicAgreementOffset6400]
  rw [Nat.le_div_iff_mul_le (by omega : 0 < 54293 + remainder)]
  omega

lemma dynamic_ideal_recursive_endpoint_exact6400 :
    dynamicCubicOwnerCap 0 = 447499 ∧
      dynamicIdealRecursiveTotal6400 219 = 274251738055574788 ∧
      dynamicIdealRecursiveTotal6400 219 < bchksResidualNumerator6400 ∧
      bchksResidualNumerator6400 -
          dynamicIdealRecursiveTotal6400 219 = 728961944425212 ∧
      dynamicIdealRecursiveTotal6400 220 = 275504028886665388 ∧
      bchksResidualNumerator6400 <
          dynamicIdealRecursiveTotal6400 220 ∧
      dynamicIdealRecursiveTotal6400 220 - bchksResidualNumerator6400 =
        523328886665388 := by
  norm_num [dynamicCubicOwnerCap, dynamicCubicGap,
    dynamicIdealRecursiveTotal6400, dynamicIdealFirstUnit6400,
    dynamicStageUnit, ceilDiv, dynamicAmbientOffset6400,
    dynamicAgreementOffset6400, dynamicLineCap6400,
    bchksHybridZMass6400, bchksHybridYMass6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400,
    bchksResidualNumerator6400]

/-- The dominant first-stage charge already exceeds the whole safe numerator
at degree `220`; no choice of later recursion schedule or terminal owner cap
can repair this within the same nonnegative ledger. -/
lemma dynamic_degree220_firstStage_alone_misses6400 :
    bchksResidualNumerator6400 <
      (dynamicIdealFirstUnit6400 + 2) * 220 * bchksHybridZMass6400 ∧
    (dynamicIdealFirstUnit6400 + 2) * 220 * bchksHybridZMass6400 -
        bchksResidualNumerator6400 = 523282839932000 := by
  norm_num [dynamicIdealFirstUnit6400, dynamicStageUnit, ceilDiv,
    dynamicAmbientOffset6400, dynamicAgreementOffset6400,
    bchksHybridZMass6400, bchksResidualNumerator6400]

end BCHKSDynamicCoreArithmetic6400
end ProximityPrize.SubmissionLower
