import ProximityPrize.SubmissionLower.BCHKSFrobeniusExactAnchorSelector6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusPrimitiveZeroIRS6401

/-!
# IRS instantiation of the sound global maximal-rank fork

This file reconciles the support-local Lagrange weights used by the
primitive-zero endpoint with the ambient parity weights used by the fixed
symbolic syndrome pencil, chooses a genuine global maximal rank, and then
uses the exact-anchor/arbitrary-column dichotomy.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusGlobalMaxRankIRS6401

open Polynomial
open scoped BigOperators
open ProximityPrize.Benchmark
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusDualGRSKernel6401
open BCHKSFrobeniusGenericRankFork6401
open BCHKSFrobeniusGenericMinor6401
open BCHKSFrobeniusGlobalMaxRankFork6401
open BCHKSFrobeniusExactAnchorSelector6401
open BCHKSFrobeniusPrimitiveZeroIRS6401
open BCHKSFrobeniusSupportStratification6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401

set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000

/-! ## Weight independence of the two-lane rank -/

def fullTwoLaneWeightedLeftFactor
    {F : Type*} [Field F] {s : Nat}
    (sigma : F →+* F) (rows : Nat) (alpha E : Fin s → F) :
    Matrix (Fin rows ⊕ Fin rows) (Fin s) F
  | Sum.inl i, j => E j * alpha j ^ i.1
  | Sum.inr i, j => sigma (E j) * alpha j ^ i.1

theorem fullTwoLaneSupportKeyMatrix_weightFactorization
    {F : Type*} [Field F] {s rows : Nat}
    (sigma : F →+* F) (alpha beta E : Fin s → F) :
    fullTwoLaneSupportKeyMatrix sigma rows alpha beta E =
      fullTwoLaneWeightedLeftFactor sigma rows alpha E *
        Matrix.diagonal beta * syndromeRightVandermonde alpha := by
  classical
  ext row col
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal]
  cases row with
  | inl i =>
      simp only [fullTwoLaneSupportKeyMatrix,
        fullTwoLaneWeightedLeftFactor, supportSyndrome,
        syndromeRightVandermonde]
      apply Finset.sum_congr rfl
      intro x hx
      rw [pow_add]
      ring
  | inr i =>
      simp only [fullTwoLaneSupportKeyMatrix,
        fullTwoLaneWeightedLeftFactor, supportSyndrome,
        syndromeRightVandermonde]
      apply Finset.sum_congr rfl
      intro x hx
      rw [pow_add]
      ring

/-- Any two everywhere-nonzero column-weight systems give the same full
two-lane rank. -/
theorem fullTwoLaneSupportKeyMatrix_rank_eq_of_nonzero_weights
    {F : Type*} [Field F] {s rows : Nat}
    (sigma : F →+* F) (alpha : Fin s ↪ F)
    (beta beta' E : Fin s → F)
    (hbeta : ∀ i, beta i ≠ 0) (hbeta' : ∀ i, beta' i ≠ 0) :
    (fullTwoLaneSupportKeyMatrix sigma rows alpha beta E).rank =
      (fullTwoLaneSupportKeyMatrix sigma rows alpha beta' E).rank := by
  classical
  have hV : IsUnit (syndromeRightVandermonde (alpha : Fin s → F)).det := by
    change IsUnit (Matrix.vandermonde (alpha : Fin s → F)).det
    exact isUnit_iff_ne_zero.mpr
      (Matrix.det_vandermonde_ne_zero_iff.mpr alpha.injective)
  have hdiag : IsUnit (Matrix.diagonal beta).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hbeta i)
  have hdiag' : IsUnit (Matrix.diagonal beta').det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun i hi ↦ hbeta' i)
  rw [fullTwoLaneSupportKeyMatrix_weightFactorization,
    fullTwoLaneSupportKeyMatrix_weightFactorization]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det
      (syndromeRightVandermonde (alpha : Fin s → F)) _ hV,
    Matrix.rank_mul_eq_left_of_isUnit_det (Matrix.diagonal beta) _ hdiag,
    Matrix.rank_mul_eq_left_of_isUnit_det
      (syndromeRightVandermonde (alpha : Fin s → F)) _ hV,
    Matrix.rank_mul_eq_left_of_isUnit_det (Matrix.diagonal beta') _ hdiag']

/-! ## Ambient-weight IRS stack -/

noncomputable def actualErrorSupportAmbientStack6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (z : IRSProfile.Field) :=
  let support := actualErrorSupportEmbedding6401 u0 u1 P z
  fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
    (support.trans IRSProfile.domain)
    (fun j ↦ syndromeWeight IRSProfile.domain (support j))
    (fun j ↦ u0 (support j) + z * u1 (support j) -
      Polynomial.eval (IRSProfile.domain (support j)) (P z))

theorem actualErrorSupportAmbientStack_rank_eq_local6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (z : IRSProfile.Field) :
    (actualErrorSupportAmbientStack6401 sigma u0 u1 P z).rank =
      (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank := by
  classical
  let support := actualErrorSupportEmbedding6401 u0 u1 P z
  let locators := support.trans IRSProfile.domain
  let E : Fin (actualErrorSupport6401 u0 u1 P z).card →
      IRSProfile.Field := fun j ↦
    u0 (support j) + z * u1 (support j) -
      Polynomial.eval (IRSProfile.domain (support j)) (P z)
  apply fullTwoLaneSupportKeyMatrix_rank_eq_of_nonzero_weights
    sigma locators
  · intro j
    exact syndromeWeight_ne_zero IRSProfile.domain (support j)
  · intro j
    exact syndromeWeight_ne_zero locators j

/-- A concrete maximal ambient-weight rank and an owner attaining it. -/
theorem exists_globalMaxAmbientRank6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (S : Finset IRSProfile.Field) (hS : S.Nonempty) :
    ∃ rho z0, z0 ∈ S ∧
      (actualErrorSupportAmbientStack6401 sigma u0 u1 P z0).rank = rho ∧
      ∀ z ∈ S,
        (actualErrorSupportAmbientStack6401 sigma u0 u1 P z).rank ≤ rho := by
  obtain ⟨z0, hz0, hmax⟩ := Finset.exists_max_image S
    (fun z ↦ (actualErrorSupportAmbientStack6401 sigma u0 u1 P z).rank) hS
  exact ⟨_, z0, hz0, rfl, hmax⟩

/-- IRS-specialized transport from a good fixed prefix minor to equality of
the ambient-weight actual-error rank.  Keeping this transport outside the
global dependent family avoids any cast through a second owner's support. -/
theorem actualErrorSupportAmbientStack_rank_eq_of_goodPrefix6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (z : IRSProfile.Field) (hz : sigma z = z ^ q6401)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hPcheck : ∀ j < keyRedundancy6401,
      (P z).natDegree + j < Fintype.card IRSProfile.Index - 1)
    (hsupport : (actualErrorSupport6401 u0 u1 P z).card ≤
      keyErrors6401)
    (hdet : Polynomial.eval z
      (genericRankKeyMinorZ6401 sigma IRSProfile.domain u0 u1 rho
        frobeniusRow).det ≠ 0)
    (hrankUpper :
      (actualErrorSupportAmbientStack6401 sigma u0 u1 P z).rank ≤
        rho) :
    (actualErrorSupportAmbientStack6401 sigma u0 u1 P z).rank =
      rho := by
  classical
  let support := actualErrorSupportEmbedding6401 u0 u1 P z
  apply ownerErrorStack_rank_eq_of_goodFixedMinor6401 sigma
    IRSProfile.domain u0 u1 hfixed rho
    (genericRankSelectedRow6401 rho frobeniusRow)
    (fun c ↦ Fin.castLE hrho (genericRankMinorColumnEquiv6401 rho c))
    hsupport z hz (P z) hPcheck support
  · intro i hi
    by_contra hne
    apply hi
    exact (mem_range_actualErrorSupportEmbedding6401
      u0 u1 P z i).2
      ((ownerError_ne_zero_iff_mem_actualErrorSupport6401
        u0 u1 P z i).1 hne)
  · have hkey :
        (fullTwoLaneKeyMatrixZ6401 sigma IRSProfile.domain u0 u1).submatrix
            (genericRankSelectedRow6401 rho frobeniusRow)
            (fun c ↦ Fin.castLE hrho
              (genericRankMinorColumnEquiv6401 rho c)) =
          genericRankKeyMinorZ6401 sigma IRSProfile.domain u0 u1 rho
            frobeniusRow := by
      ext row col
      cases row <;> rfl
    rw [hkey]
    exact hdet
  · change (actualErrorSupportAmbientStack6401 sigma u0 u1 P z).rank ≤ rho
    exact hrankUpper

/-- Cast-free IRS wrapper for the cleared-locator root equivalence at an
owner whose actual support cardinality equals the fixed minor size. -/
theorem genericRankClearedLocatorCoordinate_iff_actualErrorMem6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (rho : Nat) (hrho : rho ≤ keyErrors6401)
    (frobeniusRow : Fin (rho - keyFirstLaneRows6401) →
      Fin keyFirstLaneRows6401)
    (z : IRSProfile.Field) (hz : sigma z = z ^ q6401)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hPcheck : ∀ j < keyRedundancy6401,
      (P z).natDegree + j < Fintype.card IRSProfile.Index - 1)
    (hcard : (actualErrorSupport6401 u0 u1 P z).card = rho)
    (i : IRSProfile.Index)
    (hdet : Polynomial.eval z
      (genericRankKeyMinorZ6401 sigma IRSProfile.domain u0 u1 rho
        frobeniusRow).det ≠ 0) :
    Polynomial.eval z
        (genericRankClearedLocatorCoordinate6401 sigma IRSProfile.domain
          u0 u1 rho frobeniusRow (IRSProfile.domain i)) = 0 ↔
      i ∈ actualErrorSupport6401 u0 u1 P z := by
  classical
  let support0 := actualErrorSupportEmbedding6401 u0 u1 P z
  let supportRho : Fin rho ↪ IRSProfile.Index :=
    (finCongr hcard).symm.toEmbedding.trans support0
  have hrange : Set.range supportRho = Set.range support0 := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨(finCongr hcard).symm j, rfl⟩
    · rintro ⟨j, rfl⟩
      refine ⟨finCongr hcard j, ?_⟩
      simp [supportRho]
  have hout : ∀ x, x ∉ Set.range supportRho →
      u0 x + z * u1 x - Polynomial.eval (IRSProfile.domain x) (P z) = 0 := by
    intro x hx
    by_contra hne
    apply hx
    rw [hrange]
    exact (mem_range_actualErrorSupportEmbedding6401 u0 u1 P z x).2
      ((ownerError_ne_zero_iff_mem_actualErrorSupport6401
        u0 u1 P z x).1 hne)
  rw [genericRankClearedLocatorCoordinate_ownerError_iff6401 sigma
    IRSProfile.domain u0 u1 hfixed rho hrho frobeniusRow z hz (P z)
    hPcheck supportRho hout i hdet, hrange]
  exact mem_range_actualErrorSupportEmbedding6401 u0 u1 P z i

/-! ## Final concrete fork -/

def GlobalCommonCoreIRS6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (S : Finset IRSProfile.Field) : Prop :=
  ∃ chosen : Finset IRSProfile.Field,
    chosen ⊆ S ∧ chosen.card = weakCurveOutput6401 ∧
    132164 ≤ (Finset.univ \ chosen.biUnion
      (actualErrorSupport6401 u0 u1 P)).card ∧
    ownerDegreeCap6401 + 1 ≤ (Finset.univ \ chosen.biUnion
      (actualErrorSupport6401 u0 u1 P)).card

def GlobalDefectFamilyIRS6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (S : Finset IRSProfile.Field) : Prop :=
  ∃ T : Finset IRSProfile.Field,
    T ⊆ S ∧ defectOwnerFloor6401 ≤ T.card ∧
    ∀ z ∈ T,
      ∃ W₀ W₁ : IRSProfile.Field[X],
        W₀ ≠ 0 ∧
        W₀.degree <
          ((actualErrorSupport6401 u0 u1 P z).card -
            keyFirstLaneRows6401 : Nat) ∧
        W₁.degree <
          ((actualErrorSupport6401 u0 u1 P z).card -
            keyFirstLaneRows6401 : Nat) ∧
        TwoLaneFailureRelation sigma
          ((actualErrorSupportEmbedding6401 u0 u1 P z).trans
            IRSProfile.domain)
          (fun j ↦ u0 (actualErrorSupportEmbedding6401 u0 u1 P z j) +
            z * u1 (actualErrorSupportEmbedding6401 u0 u1 P z j) -
            Polynomial.eval
              (IRSProfile.domain
                (actualErrorSupportEmbedding6401 u0 u1 P z j)) (P z))
          W₀ W₁

/-- Fully concrete, sound global maximal-rank fork.  The exact-anchor branch
uses the prefix columns and hence locator incidence; the complementary
branch uses a cheap-row arbitrary-column maximal minor and routes every
determinant-good owner to the dual-GRS defect relation. -/
theorem globalMaxRank_commonCoreOrDefectIRS6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (hsigma : ∀ z, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (Aagree : IRSProfile.Field → Finset IRSProfile.Index)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (Aagree z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ Aagree z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i) :
    PolynomialAffineCurveWitness6401 S P ∨
      GlobalCommonCoreIRS6401 u0 u1 P S ∨
      GlobalDefectFamilyIRS6401 sigma u0 u1 P S := by
  classical
  by_cases hcurve : PolynomialAffineCurveWitness6401 S P
  · exact Or.inl hcurve
  right
  have hseedPos : 0 < weakCurveSeedInput6401 := by native_decide
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (hseedPos.trans_le hlarge)
  obtain ⟨rho, zmax, hzmax, hrankMax, hrankUpper⟩ :=
    exists_globalMaxAmbientRank6401 sigma u0 u1 P S hSnonempty
  let supportSize : IRSProfile.Field → Nat := fun z ↦
    (actualErrorSupport6401 u0 u1 P z).card
  let support : (z : IRSProfile.Field) →
      Fin (supportSize z) ↪ IRSProfile.Index :=
    actualErrorSupportEmbedding6401 u0 u1 P
  let alphaS : (z : IRSProfile.Field) →
      Fin (supportSize z) ↪ IRSProfile.Field := fun z ↦
    (support z).trans IRSProfile.domain
  let beta : (z : IRSProfile.Field) →
      Fin (supportSize z) → IRSProfile.Field := fun z j ↦
    syndromeWeight IRSProfile.domain (support z j)
  let Err : (z : IRSProfile.Field) →
      Fin (supportSize z) → IRSProfile.Field := fun z j ↦
    u0 (support z j) + z * u1 (support z j) -
      Polynomial.eval (IRSProfile.domain (support z j)) (P z)
  have hsupportUpper : ∀ z ∈ S, supportSize z ≤ keyErrors6401 := by
    intro z hz
    simpa [supportSize, keyErrors6401, bchksErrors6401] using
      actualErrorSupport_card_le_target6401 u0 u1 P Aagree z
        (hrow z hz) (howner z hz)
  have hbeta : ∀ z ∈ S, ∀ j, beta z j ≠ 0 := by
    intro z hz j
    exact syndromeWeight_ne_zero IRSProfile.domain (support z j)
  have hErr : ∀ z ∈ S, ∀ j, Err z j ≠ 0 := by
    intro z hz j
    apply (ownerError_ne_zero_iff_mem_actualErrorSupport6401
      u0 u1 P z (support z j)).2
    exact (mem_range_actualErrorSupportEmbedding6401
      u0 u1 P z (support z j)).1 ⟨j, rfl⟩
  have hout : ∀ z ∈ S, ∀ i,
      i ∉ Set.range (support z) →
        u0 i + z * u1 i - Polynomial.eval (IRSProfile.domain i) (P z) = 0 := by
    intro z hz i hi
    by_contra hne
    have himem := (ownerError_ne_zero_iff_mem_actualErrorSupport6401
      u0 u1 P z i).1 hne
    exact hi ((mem_range_actualErrorSupportEmbedding6401
      u0 u1 P z i).2 himem)
  have hrankAmbient : ∀ z ∈ S,
      (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
        (alphaS z) (beta z) (Err z)).rank ≤ rho := by
    intro z hz
    simpa [actualErrorSupportAmbientStack6401, supportSize, support,
      alphaS, beta, Err] using hrankUpper z hz
  have hrankLocal : ∀ z ∈ S,
      (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank ≤ rho := by
    intro z hz
    rw [← actualErrorSupportAmbientStack_rank_eq_local6401]
    exact hrankUpper z hz
  have hrhoRows : keyFirstLaneRows6401 + 1 ≤ rho :=
    globalRankUpperBound_ge_firstLaneRows_add_one_of_pow6401 sigma hsigma
      hfixed u0 u1 S Aagree P rho hlarge hPdegree hrow howner
      hrankLocal hcurve
  have hrho : rho ≤ keyErrors6401 := by
    have hwidth : rho ≤ supportSize zmax := by
      rw [← hrankMax]
      simpa [actualErrorSupportAmbientStack6401, supportSize, support,
        alphaS, beta, Err] using
          Matrix.rank_le_card_width
            (actualErrorSupportAmbientStack6401 sigma u0 u1 P zmax)
    exact hwidth.trans (hsupportUpper zmax hzmax)
  have hPcheck : ∀ z ∈ S, ∀ j < keyRedundancy6401,
      (P z).natDegree + j < Fintype.card IRSProfile.Index - 1 := by
    intro z hz
    exact ownerPolynomial_checkWindow6401 (by native_decide) (P z)
      (hPdegree z hz)
  by_cases hexact : ∃ z ∈ S,
      supportSize z = rho ∧
        (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
          (alphaS z) (beta z) (Err z)).rank = supportSize z
  · obtain ⟨za, hzaS, hzaSize, hzaRank⟩ := hexact
    obtain ⟨frobeniusRow, hanchorEval, hDelta, hDeltaDegree⟩ :=
      exists_nonzero_fixedPrefixMinor_of_exactRankOwner6401 sigma
        IRSProfile.domain u0 u1 hfixed (supportSize za)
        (hsupportUpper za hzaS) (by omega) za (hsigma za) (P za)
        (hPcheck za hzaS) (support za) (hout za hzaS)
        (hErr za hzaS) hzaRank
    let Delta := (genericRankKeyMinorZ6401 sigma IRSProfile.domain u0 u1
      (supportSize za) frobeniusRow).det
    let L : IRSProfile.Index → IRSProfile.Field[X] := fun i ↦
      genericRankClearedLocatorCoordinate6401 sigma IRSProfile.domain u0 u1
        (supportSize za) frobeniusRow (IRSProfile.domain i)
    have hrankGood : ∀ z ∈ determinantGoodOwners S Delta,
        (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
          (alphaS z) (beta z) (Err z)).rank = supportSize za := by
      intro z hz
      have hzS := (Finset.mem_filter.mp hz).1
      change (actualErrorSupportAmbientStack6401 sigma u0 u1 P z).rank =
        supportSize za
      apply actualErrorSupportAmbientStack_rank_eq_of_goodPrefix6401 sigma
        u0 u1 hfixed (supportSize za) (hsupportUpper za hzaS)
        frobeniusRow z (hsigma z) P (hPcheck z hzS)
        (hsupportUpper z hzS)
      · simpa [Delta, genericRankKeyMinorZ6401] using
          (Finset.mem_filter.mp hz).2
      · calc
          _ ≤ rho := hrankUpper z hzS
          _ = supportSize za := hzaSize.symm
    have hsizeGood : ∀ z ∈ determinantGoodOwners S Delta,
        supportSize z ≤ keyErrors6401 := by
      intro z hz
      exact hsupportUpper z (Finset.mem_filter.mp hz).1
    have hbetaGood : ∀ z ∈ determinantGoodOwners S Delta, ∀ j,
        beta z j ≠ 0 := by
      intro z hz j
      exact hbeta z (Finset.mem_filter.mp hz).1 j
    have hErrGood : ∀ z ∈ determinantGoodOwners S Delta, ∀ j,
        Err z j ≠ 0 := by
      intro z hz j
      exact hErr z (Finset.mem_filter.mp hz).1 j
    have hcardExact : ∀ z ∈ exactRankSupportOwners
        (determinantGoodOwners S Delta) supportSize (supportSize za),
        (actualErrorSupport6401 u0 u1 P z).card = supportSize za := by
      intro z hz
      exact (Finset.mem_filter.mp hz).2
    have hrootExact : ∀ z ∈ exactRankSupportOwners
        (determinantGoodOwners S Delta) supportSize (supportSize za),
        ∀ i ∈ actualErrorSupport6401 u0 u1 P z,
          Polynomial.eval z (L i) = 0 := by
      intro z hz i hi
      have hzGood := (Finset.mem_filter.mp hz).1
      have hzS := (Finset.mem_filter.mp hzGood).1
      apply (genericRankClearedLocatorCoordinate_iff_actualErrorMem6401
        sigma u0 u1 hfixed (supportSize za) (hsupportUpper za hzaS)
        frobeniusRow z (hsigma z) P (hPcheck z hzS)
        (Finset.mem_filter.mp hz).2 i
        (Finset.mem_filter.mp hzGood).2).2
      exact hi
    have hdegreeL : ∀ i,
        (L i).natDegree ≤ genericRankMinorDegreeCap6401 (supportSize za) := by
      intro i
      exact genericRankClearedLocatorCoordinate_degree6401 sigma
        IRSProfile.domain u0 u1 (supportSize za) frobeniusRow
          (IRSProfile.domain i)
    have hfixedExact : ∀ z ∈ exactRankSupportOwners
        (determinantGoodOwners S Delta) supportSize (supportSize za),
        fixedLocatorCoordinates L ⊆ actualErrorSupport6401 u0 u1 P z := by
      intro z hz i hi
      have hzGood := (Finset.mem_filter.mp hz).1
      have hzS := (Finset.mem_filter.mp hzGood).1
      have hLi : L i = 0 := by
        simpa [fixedLocatorCoordinates] using hi
      apply (genericRankClearedLocatorCoordinate_iff_actualErrorMem6401
        sigma u0 u1 hfixed (supportSize za) (hsupportUpper za hzaS)
        frobeniusRow z (hsigma z) P (hPcheck z hzS)
        (Finset.mem_filter.mp hz).2 i
        (Finset.mem_filter.mp hzGood).2).1
      rw [show genericRankClearedLocatorCoordinate6401 sigma
        IRSProfile.domain u0 u1 (supportSize za) frobeniusRow
          (IRSProfile.domain i) = 0 by simpa [L] using hLi,
        Polynomial.eval_zero]
    have hfork := goodPool_commonCoreOrManyFailureRelations6401 sigma
      (supportSize za) (hsupportUpper za hzaS) S Delta supportSize
      (actualErrorSupport6401 u0 u1 P) L alphaS beta Err
      (by native_decide) hlarge hDelta hDeltaDegree
      hsizeGood hbetaGood hErrGood hrankGood hcardExact hrootExact
      hdegreeL hfixedExact
    rcases hfork with hcommon | hdefect
    · left
      rcases hcommon with ⟨chosen, hchosen, hcard, hcore⟩
      refine ⟨chosen, ?_, hcard, hcore⟩
      exact hchosen.trans (fun z hz ↦
        (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1)
    · right
      rcases hdefect with ⟨hmass, hrel⟩
      refine ⟨rankDefectSupportOwners (determinantGoodOwners S Delta)
        supportSize (supportSize za), ?_, hmass, ?_⟩
      · intro z hz
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
      · intro z hz
        simpa [supportSize, support, alphaS, Err] using hrel z hz
  · have hzmaxAmbient :
        (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
          (alphaS zmax) (beta zmax) (Err zmax)).rank = rho := by
      simpa [actualErrorSupportAmbientStack6401, supportSize, support,
        alphaS, beta, Err] using hrankMax
    obtain ⟨frobeniusRow, supportColumn, hanchorEval, hDelta,
        hDeltaDegree⟩ :=
      exists_nonzero_arbitraryMinor_of_rankOwner6401 sigma IRSProfile.domain
        u0 u1 hfixed rho (by omega) (hsupportUpper zmax hzmax) zmax
        (hsigma zmax) (P zmax) (hPcheck zmax hzmax) (support zmax)
        (hout zmax hzmax) (hErr zmax hzmax) hzmaxAmbient
    let keyColumn : GenericRankMinorRow6401 rho → Fin keyErrors6401 :=
      fun col ↦ Fin.castLE (hsupportUpper zmax hzmax) (supportColumn col)
    let Delta := (arbitraryColumnKeyMinorZ6401 sigma IRSProfile.domain u0 u1
      rho frobeniusRow keyColumn).det
    have hrankGood : ∀ z ∈ determinantGoodOwners S Delta,
        (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
          (alphaS z) (beta z) (Err z)).rank = rho := by
      intro z hz
      have hzS := (Finset.mem_filter.mp hz).1
      apply ownerErrorStack_rank_eq_of_goodFixedMinor6401 sigma
        IRSProfile.domain u0 u1 hfixed rho
        (genericRankSelectedRow6401 rho frobeniusRow) keyColumn
        (hsupportUpper z hzS) z (hsigma z) (P z) (hPcheck z hzS)
        (support z) (hout z hzS)
      · simpa [Delta, arbitraryColumnKeyMinorZ6401] using
          (Finset.mem_filter.mp hz).2
      · exact hrankAmbient z hzS
    have hfork := goodPool_fullOrManyFailureRelations6401 sigma rho hrho S
      Delta supportSize alphaS beta Err hlarge hDelta hDeltaDegree
      (fun z hz ↦ hsupportUpper z (Finset.mem_filter.mp hz).1)
      (fun z hz ↦ hbeta z (Finset.mem_filter.mp hz).1)
      (fun z hz ↦ hErr z (Finset.mem_filter.mp hz).1) hrankGood
    rcases hfork with hfull | hdefect
    · exfalso
      have hempty : exactRankSupportOwners
          (determinantGoodOwners S Delta) supportSize rho = ∅ := by
        ext z
        constructor
        · intro hz
          have hzGood := (Finset.mem_filter.mp hz).1
          have hzSize := (Finset.mem_filter.mp hz).2
          have hzRank :
              (fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401
                (alphaS z) (beta z) (Err z)).rank = supportSize z :=
            (hrankGood z hzGood).trans hzSize.symm
          exact False.elim (hexact ⟨z,
            (Finset.mem_filter.mp hzGood).1, hzSize, hzRank⟩)
        · simp
      rw [hempty, Finset.card_empty] at hfull
      have : 0 < fullOwnerThreshold45_6401 := by native_decide
      omega
    · right
      rcases hdefect with ⟨hmass, hrel⟩
      refine ⟨rankDefectSupportOwners (determinantGoodOwners S Delta)
        supportSize rho, ?_, hmass, ?_⟩
      · intro z hz
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
      · intro z hz
        simpa [supportSize, support, alphaS, Err] using hrel z hz

end BCHKSFrobeniusGlobalMaxRankIRS6401
end ProximityPrize.SubmissionLower
