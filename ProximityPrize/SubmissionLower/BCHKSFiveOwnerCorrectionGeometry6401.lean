import ProximityPrize.SubmissionLower.BCHKSFrobeniusKeyEquationFork6401
import ProximityPrize.SubmissionLower.BCHKSMultiPinRankAccumulation6401
import ProximityPrize.SubmissionLower.BCHKSTupleIncidence6400

/-!
# Order-five correction geometry at score 64.01

The critical rank-two order at the score-6401 row is five.  Interpolating
five owner polynomials in the challenge therefore produces a curve of
challenge degree at most four.  This file records the exact consequences of
that unusually small degree.

The first theorem is structural: if none of the coordinate error
polynomials is identically zero, root incidence permits at most five owners
on the uncorrected core curve.  The remaining statements are exact integer
ledgers for the correction-space incidence compilers.  They intentionally do
not assert the still-missing routing theorem saying that every correction
component is proper or clone-tolerant.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFiveOwnerCorrectionGeometry6401

open Polynomial
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSTupleIncidence6400

set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000

def correctionSlopeDegree6401 : Nat := 4
def correctionRayBound6401 : Nat := 153601
def properCorrectionLastPaidDimension6401 : Nat := 97
def affineDeterminantLastPaidDimension6401 : Nat := 110
def cloneCorrectionLastPaidDimension6401 : Nat := 24

/-! ## The structured augmented determinant -/

/-- The evaluation matrix for one correction-space coordinate tuple.  The
`some j` columns are the constant evaluation vectors of a chosen correction
basis, while the `none` column is the challenge-dependent error column. -/
noncomputable def correctionAugmentedMatrix6401
    {F Coord J : Type*} [Field F] [Fintype J]
    (v : Coord → J → F) (E : Coord → F[X])
    (x : Option J → Coord) :
    Matrix (Option J) (Option J) F[X] :=
  fun i j ↦ Option.casesOn' j (E (x i))
    (fun basis ↦ Polynomial.C (v (x i) basis))

/-- The coefficient vector completing a correction to the affine error
column.  Its `none` coordinate is one, so it is always nonzero. -/
def correctionAugmentedVector6401
    {F J : Type*} [Field F] (c : J → F) : Option J → F :=
  fun j ↦ Option.casesOn' j 1 c

/-- Specializing the augmented matrix and multiplying by the correction
coefficient vector gives exactly the coordinate fitting equation. -/
theorem correctionAugmentedMatrix_mulVec6401
    {F Coord J : Type*} [Field F] [Fintype J] [DecidableEq J]
    (v : Coord → J → F) (E : Coord → F[X])
    (x : Option J → Coord) (z : F) (c : J → F)
    (i : Option J) :
    ((correctionAugmentedMatrix6401 v E x).map
        (Polynomial.evalRingHom z)).mulVec
        (correctionAugmentedVector6401 c) i =
      Polynomial.eval z (E (x i)) + ∑ j, v (x i) j * c j := by
  classical
  rw [Matrix.mulVec, dotProduct, Fintype.sum_option]
  simp only [correctionAugmentedMatrix6401,
    correctionAugmentedVector6401, Option.casesOn'_none,
    Option.casesOn'_some, Matrix.map_apply, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  simp

/-- Every fitted owner makes the specialized augmented determinant vanish.
This is division-free: the explicit kernel vector has last coordinate one. -/
theorem correctionAugmentedMatrix_det_eval_eq_zero6401
    {F Coord J : Type*} [Field F] [DecidableEq F]
    [Fintype J] [DecidableEq J]
    (v : Coord → J → F) (E : Coord → F[X])
    (x : Option J → Coord) (z : F) (c : J → F)
    (hfit : ∀ i : Option J,
      Polynomial.eval z (E (x i)) + ∑ j, v (x i) j * c j = 0) :
    ((correctionAugmentedMatrix6401 v E x).map
      (Polynomial.evalRingHom z)).det = 0 := by
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
      (i := (none : Option J))
  · funext i
    rw [correctionAugmentedMatrix_mulVec6401]
    exact hfit i
  · exact mem_nonZeroDivisors_of_ne_zero (by
      simp [correctionAugmentedVector6401])

/-- Because only the augmented error column depends on the challenge, its
determinant has degree at most four, independently of the correction-space
dimension. -/
theorem correctionAugmentedMatrix_det_natDegree_le_four6401
    {F Coord J : Type*} [Field F] [Fintype J] [DecidableEq J]
    (v : Coord → J → F) (E : Coord → F[X])
    (x : Option J → Coord)
    (hdegree : ∀ i, (E (x i)).natDegree ≤ correctionSlopeDegree6401) :
    (correctionAugmentedMatrix6401 v E x).det.natDegree ≤
      correctionSlopeDegree6401 := by
  classical
  rw [← Matrix.det_transpose]
  have hdet :=
    BCHKSGaoSpecializationCore6400.natDegree_det_le_sum_rowCaps
      (correctionAugmentedMatrix6401 v E x).transpose
      (fun j : Option J ↦ Option.casesOn' j correctionSlopeDegree6401
        (fun _ ↦ 0)) (by
          intro j i
          cases j with
          | none =>
              simpa [correctionAugmentedMatrix6401] using hdegree i
          | some j =>
              simp [correctionAugmentedMatrix6401])
  simpa [Fintype.sum_option] using hdet

/-- The promised algebraic fibre bound for a proper correction tuple.  A
nonzero augmented determinant can vanish at at most four challenges. -/
theorem properCorrectionTuple_ownerCard_le_four6401
    {F Coord J : Type*} [Field F] [DecidableEq F]
    [Fintype J] [DecidableEq J]
    (v : Coord → J → F) (E : Coord → F[X])
    (x : Option J → Coord)
    (hdegree : ∀ i, (E (x i)).natDegree ≤ correctionSlopeDegree6401)
    (hproper : (correctionAugmentedMatrix6401 v E x).det ≠ 0)
    (S : Finset F) (coeff : F → J → F)
    (hfit : ∀ z ∈ S, ∀ i : Option J,
      Polynomial.eval z (E (x i)) +
        ∑ j, v (x i) j * coeff z j = 0) :
    S.card ≤ correctionSlopeDegree6401 := by
  classical
  let D := (correctionAugmentedMatrix6401 v E x).det
  have hsub : S ⊆ D.roots.toFinset := by
    intro z hz
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hproper).2
    change Polynomial.eval z D = 0
    rw [show Polynomial.eval z D =
        ((correctionAugmentedMatrix6401 v E x).map
          (Polynomial.evalRingHom z)).det by
      exact RingHom.map_det (Polynomial.evalRingHom z)
        (correctionAugmentedMatrix6401 v E x)]
    exact correctionAugmentedMatrix_det_eval_eq_zero6401
      v E x z (coeff z) (hfit z hz)
  calc
    S.card ≤ D.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ D.roots.card := Multiset.toFinset_card_le _
    _ ≤ D.natDegree := Polynomial.card_roots' D
    _ ≤ correctionSlopeDegree6401 :=
      correctionAugmentedMatrix_det_natDegree_le_four6401
        v E x hdegree

/-! ## The core interpolant itself has no extension -/

/-- A challenge-degree-four coordinate error family with no identically-zero
coordinate can have at most five challenges carrying `185354` roots.  This
is the exact order-five specialization of the core-compatible abundance
argument. -/
theorem coreCompatibleOwners_card_le_five6401
    {F : Type} [Field F] [DecidableEq F]
    (S : Finset F) (A : F → Finset (Fin n6401))
    (E : Fin n6401 → F[X])
    (hcard : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hroot : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval z (E i) = 0)
    (hne : ∀ i, E i ≠ 0)
    (hdegree : ∀ i, (E i).natDegree ≤ correctionSlopeDegree6401) :
    S.card ≤ 5 := by
  classical
  have hfixed : fixedLocatorCoordinates E = (∅ : Finset (Fin n6401)) := by
    ext i
    simp [fixedLocatorCoordinates, hne i]
  have hinc := locator_root_incidence S A E a6401
    correctionSlopeDegree6401 hcard hroot hdegree
  rw [hfixed] at hinc
  simp only [Finset.card_empty, Nat.sub_zero] at hinc
  norm_num [a6401, n6401, correctionSlopeDegree6401] at hinc ⊢
  omega

/-! ## Exact correction-space ledgers -/

/-- The component-free correction-ray compiler is

`2(n-a+1) + floor(4 * choose(n,2) / ((k-1)(a-k+1)))`.

At this row its second term is only `19`. -/
theorem correctionRay_exact6401 :
    4 * Nat.choose n6401 2 /
        ((ownerDegreeCap6401) * (a6401 - ownerDegreeCap6401)) = 19 ∧
      2 * (n6401 - a6401 + 1) +
          4 * Nat.choose n6401 2 /
            ((ownerDegreeCap6401) *
              (a6401 - ownerDegreeCap6401)) = correctionRayBound6401 := by
  native_decide

/-- For a proper correction space of dimension `s`, the projective
intersection compiler compares

`4(s+1) * choose(n,s+1)` with `B * choose(a,s+1)`.

It pays every dimension through `97`. -/
theorem properCorrection_dimension97_paid6401 :
    correctionSlopeDegree6401 *
        (properCorrectionLastPaidDimension6401 + 1) *
          Nat.choose n6401 (properCorrectionLastPaidDimension6401 + 1) <=
      weakCurveSeedCap6401 *
        Nat.choose a6401 (properCorrectionLastPaidDimension6401 + 1) := by
  native_decide

/-- Dimension `98` is the first miss for the same proper-intersection
compiler, so `97` is a genuine arithmetic boundary. -/
theorem properCorrection_dimension98_misses6401 :
    weakCurveSeedCap6401 *
        Nat.choose a6401 (properCorrectionLastPaidDimension6401 + 2) <
      correctionSlopeDegree6401 *
        (properCorrectionLastPaidDimension6401 + 2) *
          Nat.choose n6401 (properCorrectionLastPaidDimension6401 + 2) := by
  native_decide

/-- The coordinate equations have more structure than arbitrary divisors on
`P^1 x P^s`: all correction coefficients are constant in the challenge and
only the augmented error column has degree four.  Once an `s`-coordinate
evaluation basis has been chosen, the final determinant therefore has degree
at most four, rather than `4*(s+1)`.  The sharpened affine determinant ledger
pays through dimension `110`. -/
theorem affineDeterminant_dimension110_paid6401 :
    correctionSlopeDegree6401 *
        Nat.choose n6401 (affineDeterminantLastPaidDimension6401 + 1) <=
      weakCurveSeedCap6401 *
        Nat.choose a6401 (affineDeterminantLastPaidDimension6401 + 1) := by
  native_decide

/-- Dimension `111` is the first miss for the structured affine-determinant
count. -/
theorem affineDeterminant_dimension111_misses6401 :
    weakCurveSeedCap6401 *
        Nat.choose a6401 (affineDeterminantLastPaidDimension6401 + 2) <
      correctionSlopeDegree6401 *
        Nat.choose n6401 (affineDeterminantLastPaidDimension6401 + 2) := by
  native_decide

/-- Combinatorial consumer for the sharpened determinant bound.  If every
`111`-coordinate tuple belongs to at most four owner supports, then the
entire owner family is already below the weak-seed cap.  A proper
dimension-`110` correction space supplies exactly this fibre hypothesis by
solving on an evaluation basis and taking one degree-four augmented
determinant. -/
theorem ownerCard_le_seedCap_of_111tupleFibers6401
    {Coord Owner : Type*} [Fintype Coord]
    [DecidableEq Coord] [DecidableEq Owner]
    (U : Finset Coord) (S : Finset Owner) (A : Owner → Finset Coord)
    (hU : U.card = n6401)
    (hsub : ∀ z ∈ S, A z ⊆ U)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hfiber : ∀ T ∈ U.powersetCard
        (affineDeterminantLastPaidDimension6401 + 1),
      (S.filter fun z ↦ T ⊆ A z).card ≤ correctionSlopeDegree6401) :
    S.card ≤ weakCurveSeedCap6401 := by
  have hinc := card_mul_choose_le_of_tupleFibers U S A a6401
    (affineDeterminantLastPaidDimension6401 + 1)
    correctionSlopeDegree6401 hsub hrow hfiber
  rw [hU] at hinc
  have hmul :
      S.card * Nat.choose a6401
          (affineDeterminantLastPaidDimension6401 + 1) ≤
        weakCurveSeedCap6401 * Nat.choose a6401
          (affineDeterminantLastPaidDimension6401 + 1) :=
    hinc.trans affineDeterminant_dimension110_paid6401
  exact le_of_mul_le_mul_right hmul (Nat.choose_pos (by
    norm_num [a6401, affineDeterminantLastPaidDimension6401]))

/-- At exact RS minimum support, one basis curve contains at most

`floor(4 * (n-k+1) / (a-k+1)) = 9`

rich parameter points. -/
theorem cloneCurveMultiplicity_exact6401 :
    correctionSlopeDegree6401 * (n6401 - ownerDegreeCap6401) /
        (a6401 - ownerDegreeCap6401) = 9 := by
  native_decide

/-- The clone-tolerant basis-curve compiler pays correction dimension `24`.
The division-free comparison uses the ambient falling factorial and the
restricted generalized-weight rising factorial. -/
theorem cloneCorrection_dimension24_paid6401 :
    9 * n6401.descFactorial cloneCorrectionLastPaidDimension6401 <=
      weakCurveSeedCap6401 *
        (a6401 - ownerDegreeCap6401).ascFactorial
          cloneCorrectionLastPaidDimension6401 := by
  native_decide

/-- Dimension `25` is the adjacent failure of the clone-tolerant compiler. -/
theorem cloneCorrection_dimension25_misses6401 :
    weakCurveSeedCap6401 *
        (a6401 - ownerDegreeCap6401).ascFactorial
          (cloneCorrectionLastPaidDimension6401 + 1) <
      9 * n6401.descFactorial
        (cloneCorrectionLastPaidDimension6401 + 1) := by
  native_decide

/-- Compact statement of all order-five numerical transitions. -/
theorem correctionGeometry_parameterLedger6401 :
    correctionSlopeDegree6401 = 4 ∧
      correctionRayBound6401 = 153601 ∧
      properCorrectionLastPaidDimension6401 = 97 ∧
      affineDeterminantLastPaidDimension6401 = 110 ∧
      cloneCorrectionLastPaidDimension6401 = 24 := by
  native_decide

end BCHKSFiveOwnerCorrectionGeometry6401
end ProximityPrize.SubmissionLower
