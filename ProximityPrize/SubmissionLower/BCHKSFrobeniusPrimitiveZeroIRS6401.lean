import ProximityPrize.SubmissionLower.BCHKSFrobeniusPrimitiveZeroExtraction6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusSupportStratification6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusGenericRankFork6401

/-!
# IRS adapter and exact rank-zero-excess fork

This file enumerates each literal nonzero error support by `Fin s`, applies
the primitive-zero extraction with no abstract support hypotheses left, and
exports the exact family fork.  Under failure of the weak curve witness, the
new-radius owners whose full two-lane stack has rank exactly the ordinary
row count form a set smaller than the weak seed.  Every other new-radius
owner has rank at least `54283`.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusPrimitiveZeroIRS6401

open Polynomial
open ProximityPrize.Benchmark
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusGenericRankFork6401
open BCHKSFrobeniusDualGRSKernel6401
open BCHKSFrobeniusSupportStratification6401
open BCHKSFrobeniusPrimitiveZeroExtraction6401
open BCHKSFrobeniusProjectiveAffineLine6401
open BCHKSFrobeniusConstantPairClosure6401
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401

set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000

/-- The fixed points of a power endomorphism are among the roots of
`X^p-X`, so there are at most `p` of them. -/
theorem frobeniusFixedScalars_card_le_of_pow
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (p : Nat) (hp : 1 < p) (sigma : F →+* F)
    (hsigma : ∀ z, sigma z = z ^ p) :
    (frobeniusFixedScalars sigma).card ≤ p := by
  classical
  let W : Polynomial F := (Polynomial.X : Polynomial F) ^ p - Polynomial.X
  have hdeg : W.natDegree = p := by
    exact FiniteField.X_pow_card_sub_X_natDegree_eq F hp
  by_contra hnot
  have hcard : W.natDegree < (frobeniusFixedScalars sigma).card := by
    rw [hdeg]
    omega
  have hzero : W = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      W (frobeniusFixedScalars sigma)
    · intro z hzmem
      have hz : sigma z = z := by
        change z ∈ Finset.univ.filter (fun x ↦ sigma x = x) at hzmem
        exact (Finset.mem_filter.mp hzmem).2
      simp only [W, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X]
      rw [← hsigma z, hz, sub_self]
    · exact hcard
  have hne : W ≠ 0 := by
    exact FiniteField.X_pow_card_sub_X_ne_zero F hp
  exact hne hzero

/-- For the benchmark Frobenius, the fixed-scalar cardinality bound used by
the projective-line argument is automatic. -/
theorem frobeniusFixedScalars_card_le_q6401_of_pow
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (hsigma : ∀ z, sigma z = z ^ q6401) :
    (frobeniusFixedScalars sigma).card ≤ q6401 :=
  frobeniusFixedScalars_card_le_of_pow q6401 (by native_decide) sigma hsigma

/-- Canonical enumeration of the literal nonzero error support. -/
noncomputable def actualErrorSupportEmbedding6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (z : IRSProfile.Field) :
    Fin (actualErrorSupport6401 u0 u1 P z).card ↪ IRSProfile.Index := by
  let E := actualErrorSupport6401 u0 u1 P z
  let e : Fin E.card ≃ E :=
    (Finset.equivFinOfCardEq (rfl : E.card = E.card)).symm
  exact e.toEmbedding.trans (Function.Embedding.subtype _)

theorem mem_range_actualErrorSupportEmbedding6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (z : IRSProfile.Field) (i : IRSProfile.Index) :
    i ∈ Set.range (actualErrorSupportEmbedding6401 u0 u1 P z) ↔
      i ∈ actualErrorSupport6401 u0 u1 P z := by
  classical
  let E := actualErrorSupport6401 u0 u1 P z
  let e : Fin E.card ≃ E :=
    (Finset.equivFinOfCardEq (rfl : E.card = E.card)).symm
  change i ∈ Set.range
      (e.toEmbedding.trans (Function.Embedding.subtype _)) ↔ i ∈ E
  constructor
  · rintro ⟨j, rfl⟩
    exact (e j).2
  · intro hi
    refine ⟨e.symm ⟨i, hi⟩, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)

/-- Membership in the literal error support is exactly nonvanishing of the
zero-extended owner error. -/
theorem ownerError_ne_zero_iff_mem_actualErrorSupport6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (z : IRSProfile.Field) (i : IRSProfile.Index) :
    u0 i + z * u1 i - Polynomial.eval (IRSProfile.domain i) (P z) ≠ 0 ↔
      i ∈ actualErrorSupport6401 u0 u1 P z := by
  classical
  simp only [actualErrorSupport6401, actualAgreementSet6401,
    Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter,
    sub_ne_zero]
  exact ne_comm

/-- The literal support stack, using its own nonzero Lagrange weights. -/
noncomputable def actualErrorSupportFullStack6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (z : IRSProfile.Field) :=
  let support := actualErrorSupportEmbedding6401 u0 u1 P z
  let locators := support.trans IRSProfile.domain
  fullTwoLaneSupportKeyMatrix sigma keyFirstLaneRows6401 locators
    (fun j ↦ syndromeWeight locators j)
    (fun j ↦ u0 (support j) + z * u1 (support j) -
      Polynomial.eval (IRSProfile.domain (support j)) (P z))

/-- Every new-radius owner has enough actual errors for the ordinary lane to
have all `54282` independent rows. -/
theorem firstLaneRows_lt_actualErrorSupport_card_of_nonOld6401
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (z : IRSProfile.Field)
    (hz : z ∈ S \ oldRadiusOwners6401 u0 u1 P S) :
    keyFirstLaneRows6401 < (actualErrorSupport6401 u0 u1 P z).card := by
  have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
  have hzold : z ∉ oldRadiusOwners6401 u0 u1 P S :=
    (Finset.mem_sdiff.mp hz).2
  have herr : bchksErrors6399 <
      (actualErrorSupport6401 u0 u1 P z).card := by
    by_contra h
    have hle : (actualErrorSupport6401 u0 u1 P z).card ≤
        bchksErrors6399 := by omega
    exact hzold (Finset.mem_filter.mpr ⟨hzS, hle⟩)
  norm_num [keyFirstLaneRows6401, keyRedundancy6401, keyErrors6401,
    bchksErrors6399, bchksErrors6401, n6401, ownerDegreeCap6401] at herr ⊢
  omega

/-- The ordinary submatrix forces every new-radius full stack to have rank
at least `54282`. -/
theorem actualErrorSupportFullStack_rank_ge_firstLaneRows6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (z : IRSProfile.Field)
    (hz : z ∈ S \ oldRadiusOwners6401 u0 u1 P S) :
    keyFirstLaneRows6401 ≤
      (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank := by
  classical
  let support := actualErrorSupportEmbedding6401 u0 u1 P z
  let locators := support.trans IRSProfile.domain
  let E : Fin (actualErrorSupport6401 u0 u1 P z).card →
      IRSProfile.Field := fun j ↦
    u0 (support j) + z * u1 (support j) -
      Polynomial.eval (IRSProfile.domain (support j)) (P z)
  let beta : Fin (actualErrorSupport6401 u0 u1 P z).card →
      IRSProfile.Field := fun j ↦ syndromeWeight locators j
  have hE : ∀ j, E j ≠ 0 := by
    intro j
    apply (ownerError_ne_zero_iff_mem_actualErrorSupport6401
      u0 u1 P z (support j)).2
    exact (mem_range_actualErrorSupportEmbedding6401
      u0 u1 P z (support j)).1 ⟨j, rfl⟩
  have hordinary :
      (supportSyndromeMatrix keyFirstLaneRows6401
        (actualErrorSupport6401 u0 u1 P z).card locators
        (fun j ↦ beta j * E j)).rank = keyFirstLaneRows6401 := by
    apply supportSyndromeMatrix_rank_eq_rows
    · exact locators.injective
    · intro j
      exact mul_ne_zero (syndromeWeight_ne_zero locators j) (hE j)
    · exact (firstLaneRows_lt_actualErrorSupport_card_of_nonOld6401
        u0 u1 S P z hz).le
  have hsub := Matrix.rank_submatrix_le
    (actualErrorSupportFullStack6401 sigma u0 u1 P z) Sum.inl
      (id : Fin (actualErrorSupport6401 u0 u1 P z).card →
        Fin (actualErrorSupport6401 u0 u1 P z).card)
  change (supportSyndromeMatrix keyFirstLaneRows6401
      (actualErrorSupport6401 u0 u1 P z).card locators
      (fun j ↦ beta j * E j)).rank ≤
        (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank at hsub
  rwa [hordinary] at hsub

/-- The new-radius owners in the now-closed zero-excess rank stratum. -/
noncomputable def zeroExcessNewRadiusOwners6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field) :
    Finset IRSProfile.Field :=
  (S \ oldRadiusOwners6401 u0 u1 P S).filter fun z ↦
    (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank =
      keyFirstLaneRows6401

private theorem polynomialAffineCurveWitness_mono6401
    {F : Type*} [Field F] {T S : Finset F} {P : F → Polynomial F}
    (hTS : T ⊆ S) (hcurve : PolynomialAffineCurveWitness6401 T P) :
    PolynomialAffineCurveWitness6401 S P := by
  rcases hcurve with ⟨p0, p1, hp0, hp1, U, hUT, hUcard, hline⟩
  exact ⟨p0, p1, hp0, hp1, U, hUT.trans hTS, hUcard, hline⟩

/-- Sharp global cap for all new-radius rank-`54282` owners at once.  The
literal supports may have any of the twenty new sizes, and no support-size
or rank pigeonhole is paid before the degree-zero endpoint. -/
theorem zeroExcessNewRadiusOwners_card_le_constantPrimitiveFamilyCap6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (Aagree : IRSProfile.Field → Finset IRSProfile.Index)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (Aagree z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ Aagree z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    (zeroExcessNewRadiusOwners6401 sigma u0 u1 S P).card ≤
      constantPrimitiveFamilyCap6401 := by
  classical
  let R := zeroExcessNewRadiusOwners6401 sigma u0 u1 S P
  have hRS : R ⊆ S := by
    intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
  have hfailR : ¬ PolynomialAffineCurveWitness6401 R P := by
    intro hcurveR
    exact hfail (polynomialAffineCurveWitness_mono6401 hRS hcurveR)
  apply rankEqualFirstLaneRowsOwners_card_le_cap6401_of_no_curve
    sigma IRSProfile.domain hfixed hfixedCard u0 u1 R Aagree P
      (supportSize := fun z ↦ (actualErrorSupport6401 u0 u1 P z).card)
      (support := actualErrorSupportEmbedding6401 u0 u1 P)
      (hfail := hfailR)
  · intro z hz
    exact hPdegree z (hRS hz)
  · intro z hz
    exact hrow z (hRS hz)
  · intro z hz i hi
    exact howner z (hRS hz) i hi
  · intro z hz i
    exact (ownerError_ne_zero_iff_mem_actualErrorSupport6401
      u0 u1 P z i).trans
        (mem_range_actualErrorSupportEmbedding6401 u0 u1 P z i).symm
  · intro z hz
    exact firstLaneRows_lt_actualErrorSupport_card_of_nonOld6401
      u0 u1 S P z (Finset.mem_filter.mp hz).1
  · intro z hz
    exact actualErrorSupport_card_le_target6401 u0 u1 P Aagree z
      (hrow z (hRS hz)) (howner z (hRS hz))
  · intro z hz
    exact (Finset.mem_filter.mp hz).2

/-- Under no global curve, fewer than one weak seed of new-radius owners can
remain in the rank-`54282` stratum.  All support enumeration, nonzero-error,
and size conditions are discharged from the literal IRS family. -/
theorem zeroExcessNewRadiusOwners_card_lt_weakSeed6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (Aagree : IRSProfile.Field → Finset IRSProfile.Index)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (Aagree z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ Aagree z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    (zeroExcessNewRadiusOwners6401 sigma u0 u1 S P).card <
      weakCurveSeedInput6401 := by
  classical
  let R := zeroExcessNewRadiusOwners6401 sigma u0 u1 S P
  by_contra hnot
  have hRlarge : weakCurveSeedInput6401 ≤ R.card := by
    have h := Nat.le_of_not_gt hnot
    simpa [R] using h
  have hRS : R ⊆ S := by
    intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1
  have hcurveR : PolynomialAffineCurveWitness6401 R P := by
    apply rankEqualFirstLaneRowsOwners_ownerCurve6401
      sigma IRSProfile.domain hfixed hfixedCard u0 u1 R Aagree P
      hRlarge
      (supportSize := fun z ↦ (actualErrorSupport6401 u0 u1 P z).card)
      (support := actualErrorSupportEmbedding6401 u0 u1 P)
    · intro z hz
      exact hPdegree z (hRS hz)
    · intro z hz
      exact hrow z (hRS hz)
    · intro z hz i hi
      exact howner z (hRS hz) i hi
    · intro z hz i
      exact (ownerError_ne_zero_iff_mem_actualErrorSupport6401
        u0 u1 P z i).trans
          (mem_range_actualErrorSupportEmbedding6401 u0 u1 P z i).symm
    · intro z hz
      exact firstLaneRows_lt_actualErrorSupport_card_of_nonOld6401
        u0 u1 S P z (Finset.mem_filter.mp hz).1
    · intro z hz
      exact actualErrorSupport_card_le_target6401 u0 u1 P Aagree z
        (hrow z (hRS hz)) (howner z (hRS hz))
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  exact hfail (polynomialAffineCurveWitness_mono6401 hRS hcurveR)

/-- Outside the small zero-excess stratum, every new-radius owner has
positive excess rank, i.e. rank at least `54283`. -/
theorem rank_ge_firstLaneRows_add_one_of_mem_residual6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (z : IRSProfile.Field)
    (hz : z ∈ (S \ oldRadiusOwners6401 u0 u1 P S) \
      zeroExcessNewRadiusOwners6401 sigma u0 u1 S P) :
    keyFirstLaneRows6401 + 1 ≤
      (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank := by
  have hznew : z ∈ S \ oldRadiusOwners6401 u0 u1 P S :=
    (Finset.mem_sdiff.mp hz).1
  have hge := actualErrorSupportFullStack_rank_ge_firstLaneRows6401
    sigma u0 u1 S P z hznew
  have hne : (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank ≠
      keyFirstLaneRows6401 := by
    intro heq
    exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_filter.mpr ⟨hznew, heq⟩)
  omega

/-- A global rank upper bound for the unsplit owner pool must be at least
`54283`.  If it were at most `54282`, every new-radius owner would lie in
the sharply capped zero-excess stratum; together with the old-radius cap,
this is far smaller than the original owner pool.  Thus a maximal-rank
minor can be selected on the full pool without first discarding either
stratum. -/
theorem globalRankUpperBound_ge_firstLaneRows_add_one6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (Aagree : IRSProfile.Field → Finset IRSProfile.Index)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (rho : Nat)
    (hlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (Aagree z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ Aagree z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i)
    (hrankUpper : ∀ z ∈ S,
      (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank ≤ rho)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    keyFirstLaneRows6401 + 1 ≤ rho := by
  classical
  by_contra hnot
  have hrho : rho ≤ keyFirstLaneRows6401 := by omega
  let O := oldRadiusOwners6401 u0 u1 P S
  let N := S \ O
  let Zowners := zeroExcessNewRadiusOwners6401 sigma u0 u1 S P
  have hOS : O ⊆ S := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  have hNZ : N ⊆ Zowners := by
    intro z hz
    have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
    have hznew : z ∈ S \ oldRadiusOwners6401 u0 u1 P S := by
      simpa [N, O] using hz
    have hge := actualErrorSupportFullStack_rank_ge_firstLaneRows6401
      sigma u0 u1 S P z hznew
    have hle := (hrankUpper z hzS).trans hrho
    have heq : (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank =
        keyFirstLaneRows6401 := Nat.le_antisymm hle hge
    exact Finset.mem_filter.mpr ⟨hznew, heq⟩
  have hOcap : O.card ≤ bchksNumerator6399 := by
    simpa [O] using oldRadiusOwners_card_le_6399_of_no_curve6401
      u0 u1 S P hPdegree hfail
  have hZcap : Zowners.card ≤ constantPrimitiveFamilyCap6401 := by
    simpa [Zowners] using
      zeroExcessNewRadiusOwners_card_le_constantPrimitiveFamilyCap6401
        sigma hfixed hfixedCard u0 u1 S Aagree P hPdegree hrow howner hfail
  have hNcap : N.card ≤ constantPrimitiveFamilyCap6401 :=
    (Finset.card_le_card hNZ).trans hZcap
  have hpartition : S.card = O.card + N.card := by
    have hOcard : O.card ≤ S.card := Finset.card_le_card hOS
    dsimp [N]
    rw [Finset.card_sdiff_of_subset hOS]
    omega
  have hnum : bchksNumerator6399 + constantPrimitiveFamilyCap6401 <
      weakCurveSeedInput6401 := by
    native_decide
  omega

/-- Benchmark-power-law wrapper for the unsplit global-rank lower bound. -/
theorem globalRankUpperBound_ge_firstLaneRows_add_one_of_pow6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (hsigma : ∀ z, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (Aagree : IRSProfile.Field → Finset IRSProfile.Index)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (rho : Nat)
    (hlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (Aagree z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ Aagree z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i)
    (hrankUpper : ∀ z ∈ S,
      (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank ≤ rho)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    keyFirstLaneRows6401 + 1 ≤ rho := by
  exact globalRankUpperBound_ge_firstLaneRows_add_one6401 sigma hfixed
    (frobeniusFixedScalars_card_le_q6401_of_pow sigma hsigma)
    u0 u1 S Aagree P rho hlarge hPdegree hrow howner hrankUpper hfail

/-- After deleting the old-radius owners and the entire rank-zero-excess
stratum, the positive-rank residual retains essentially all owner mass. -/
theorem positiveExcessNewRadiusOwners_card_lower6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (Aagree : IRSProfile.Field → Finset IRSProfile.Index)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (Aagree z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ Aagree z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    weakCurveSeedInput6401 - bchksNumerator6399 -
        constantPrimitiveFamilyCap6401 ≤
      ((S \ oldRadiusOwners6401 u0 u1 P S) \
        zeroExcessNewRadiusOwners6401 sigma u0 u1 S P).card := by
  let N := S \ oldRadiusOwners6401 u0 u1 P S
  let Zowners := zeroExcessNewRadiusOwners6401 sigma u0 u1 S P
  have hZN : Zowners ⊆ N := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  have hN : weakCurveSeedInput6401 - bchksNumerator6399 ≤ N.card := by
    simpa [N] using nonOldRadiusOwners_card_lower6401
      u0 u1 S P hlarge hPdegree hfail
  have hZ : Zowners.card ≤ constantPrimitiveFamilyCap6401 := by
    simpa [Zowners] using
      zeroExcessNewRadiusOwners_card_le_constantPrimitiveFamilyCap6401
        sigma hfixed hfixedCard u0 u1 S Aagree P hPdegree hrow howner hfail
  change weakCurveSeedInput6401 - bchksNumerator6399 -
      constantPrimitiveFamilyCap6401 ≤ (N \ Zowners).card
  rw [Finset.card_sdiff_of_subset hZN]
  omega

theorem positiveExcessNewRadiusOwners_floor_exact6401 :
    weakCurveSeedInput6401 - bchksNumerator6399 -
      constantPrimitiveFamilyCap6401 = 185800451149971548 := by
  native_decide

/-- Unsplit maximal-rank-ready fork.  Either the target curve exists, or the
whole rank-`54282` stratum costs only `20,148,187,609` owners and the
remaining `185,800,451,149,971,548` owners all have rank at least `54283`.
-/
theorem zeroExcessOrPositiveRank_sharpMassFork6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
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
      ((zeroExcessNewRadiusOwners6401 sigma u0 u1 S P).card ≤
          constantPrimitiveFamilyCap6401 ∧
        185800451149971548 ≤
          ((S \ oldRadiusOwners6401 u0 u1 P S) \
            zeroExcessNewRadiusOwners6401 sigma u0 u1 S P).card ∧
        ∀ z ∈ (S \ oldRadiusOwners6401 u0 u1 P S) \
            zeroExcessNewRadiusOwners6401 sigma u0 u1 S P,
          keyFirstLaneRows6401 + 1 ≤
            (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank) := by
  classical
  by_cases hcurve : PolynomialAffineCurveWitness6401 S P
  · exact Or.inl hcurve
  · right
    refine ⟨
      zeroExcessNewRadiusOwners_card_le_constantPrimitiveFamilyCap6401
        sigma hfixed hfixedCard u0 u1 S Aagree P hPdegree hrow howner hcurve,
      ?_, fun z hz ↦ rank_ge_firstLaneRows_add_one_of_mem_residual6401
        sigma u0 u1 S P z hz⟩
    rw [← positiveExcessNewRadiusOwners_floor_exact6401]
    exact positiveExcessNewRadiusOwners_card_lower6401 sigma hfixed
      hfixedCard u0 u1 S Aagree P hlarge hPdegree hrow howner hcurve

/-- Primary exact fork: either the desired weak curve already exists, or
the rank-`m` new-radius stratum is sub-seed and the remaining residual is
literally `rho >= m+1`. -/
theorem zeroExcessOrPositiveRank_weakSeedFork6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (Aagree : IRSProfile.Field → Finset IRSProfile.Index)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (Aagree z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ Aagree z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i) :
    PolynomialAffineCurveWitness6401 S P ∨
      ((zeroExcessNewRadiusOwners6401 sigma u0 u1 S P).card <
          weakCurveSeedInput6401 ∧
        ∀ z ∈ (S \ oldRadiusOwners6401 u0 u1 P S) \
            zeroExcessNewRadiusOwners6401 sigma u0 u1 S P,
          keyFirstLaneRows6401 + 1 ≤
            (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank) := by
  classical
  by_cases hcurve : PolynomialAffineCurveWitness6401 S P
  · exact Or.inl hcurve
  · exact Or.inr ⟨
      zeroExcessNewRadiusOwners_card_lt_weakSeed6401 sigma hfixed
        hfixedCard u0 u1 S Aagree P hPdegree hrow howner hcurve,
      fun z hz ↦ rank_ge_firstLaneRows_add_one_of_mem_residual6401
        sigma u0 u1 S P z hz⟩

/-- Per-`(s,rho)` form for direct composition with exact-support and rank
pigeonholing.  A weak-seed-sized family of one new error weight and one full
stack rank either already supplies the global curve or has `rho >= m+1`.
There is no residual `rho=m` branch. -/
theorem exactWeightExactRank_weakSeedFork6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤ q6401)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S T : Finset IRSProfile.Field)
    (Aagree : IRSProfile.Field → Finset IRSProfile.Index)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (s rho : Nat) (hs : s ∈ newErrorWeights6401)
    (hTS : T ⊆ S) (hTlarge : weakCurveSeedInput6401 ≤ T.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (Aagree z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ Aagree z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i)
    (hweight : ∀ z ∈ T,
      (actualErrorSupport6401 u0 u1 P z).card = s)
    (hrank : ∀ z ∈ T,
      (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank = rho) :
    PolynomialAffineCurveWitness6401 S P ∨
      keyFirstLaneRows6401 + 1 ≤ rho := by
  classical
  have hslo : bchksErrors6399 < s := by
    have := (Finset.mem_Icc.mp hs).1
    omega
  have hznew : ∀ z ∈ T,
      z ∈ S \ oldRadiusOwners6401 u0 u1 P S := by
    intro z hz
    refine Finset.mem_sdiff.mpr ⟨hTS hz, ?_⟩
    intro hzold
    have hle := (Finset.mem_filter.mp hzold).2
    rw [hweight z hz] at hle
    omega
  have hTpos : 0 < T.card := by
    have hseedpos : 0 < weakCurveSeedInput6401 := by native_decide
    exact hseedpos.trans_le hTlarge
  obtain ⟨z0, hz0⟩ := Finset.card_pos.mp hTpos
  have hrhoLower : keyFirstLaneRows6401 ≤ rho := by
    have hge := actualErrorSupportFullStack_rank_ge_firstLaneRows6401
      sigma u0 u1 S P z0 (hznew z0 hz0)
    rw [hrank z0 hz0] at hge
    exact hge
  by_cases hpositive : keyFirstLaneRows6401 + 1 ≤ rho
  · exact Or.inr hpositive
  · have hrhoeq : rho = keyFirstLaneRows6401 := by omega
    apply Or.inl
    apply polynomialAffineCurveWitness_mono6401 hTS
    apply rankEqualFirstLaneRowsOwners_ownerCurve6401
      sigma IRSProfile.domain hfixed hfixedCard u0 u1 T Aagree P
      hTlarge
      (supportSize := fun z ↦ (actualErrorSupport6401 u0 u1 P z).card)
      (support := actualErrorSupportEmbedding6401 u0 u1 P)
    · intro z hz
      exact hPdegree z (hTS hz)
    · intro z hz
      exact hrow z (hTS hz)
    · intro z hz i hi
      exact howner z (hTS hz) i hi
    · intro z hz i
      exact (ownerError_ne_zero_iff_mem_actualErrorSupport6401
        u0 u1 P z i).trans
          (mem_range_actualErrorSupportEmbedding6401 u0 u1 P z i).symm
    · intro z hz
      exact firstLaneRows_lt_actualErrorSupport_card_of_nonOld6401
        u0 u1 S P z (hznew z hz)
    · intro z hz
      exact actualErrorSupport_card_le_target6401 u0 u1 P Aagree z
        (hrow z (hTS hz)) (howner z (hTS hz))
    · intro z hz
      change (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank =
        keyFirstLaneRows6401
      exact (hrank z hz).trans hrhoeq

/-- IRS-facing version of the primary fork.  The benchmark power law
discharges the fixed-scalar cardinality premise internally. -/
theorem zeroExcessOrPositiveRank_weakSeedFork_of_pow6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (hsigma : ∀ z, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S : Finset IRSProfile.Field)
    (Aagree : IRSProfile.Field → Finset IRSProfile.Index)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (Aagree z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ Aagree z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i) :
    PolynomialAffineCurveWitness6401 S P ∨
      ((zeroExcessNewRadiusOwners6401 sigma u0 u1 S P).card <
          weakCurveSeedInput6401 ∧
        ∀ z ∈ (S \ oldRadiusOwners6401 u0 u1 P S) \
            zeroExcessNewRadiusOwners6401 sigma u0 u1 S P,
          keyFirstLaneRows6401 + 1 ≤
            (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank) := by
  exact zeroExcessOrPositiveRank_weakSeedFork6401 sigma hfixed
    (frobeniusFixedScalars_card_le_q6401_of_pow sigma hsigma)
    u0 u1 S Aagree P hPdegree hrow howner

/-- IRS-facing per-`(s,rho)` fork with the fixed-scalar cardinality premise
derived from the benchmark power law. -/
theorem exactWeightExactRank_weakSeedFork_of_pow6401
    (sigma : IRSProfile.Field →+* IRSProfile.Field)
    (hsigma : ∀ z, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (IRSProfile.domain i) = IRSProfile.domain i)
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (S T : Finset IRSProfile.Field)
    (Aagree : IRSProfile.Field → Finset IRSProfile.Index)
    (P : IRSProfile.Field → Polynomial IRSProfile.Field)
    (s rho : Nat) (hs : s ∈ newErrorWeights6401)
    (hTS : T ⊆ S) (hTlarge : weakCurveSeedInput6401 ≤ T.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (Aagree z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ Aagree z,
      Polynomial.eval (IRSProfile.domain i) (P z) = u0 i + z * u1 i)
    (hweight : ∀ z ∈ T,
      (actualErrorSupport6401 u0 u1 P z).card = s)
    (hrank : ∀ z ∈ T,
      (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank = rho) :
    PolynomialAffineCurveWitness6401 S P ∨
      keyFirstLaneRows6401 + 1 ≤ rho := by
  exact exactWeightExactRank_weakSeedFork6401 sigma hfixed
    (frobeniusFixedScalars_card_le_q6401_of_pow sigma hsigma)
    u0 u1 S T Aagree P s rho hs hTS hTlarge hPdegree hrow howner
    hweight hrank

/-- Benchmark-power-law version of the unsplit sharp mass fork. -/
theorem zeroExcessOrPositiveRank_sharpMassFork_of_pow6401
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
      ((zeroExcessNewRadiusOwners6401 sigma u0 u1 S P).card ≤
          constantPrimitiveFamilyCap6401 ∧
        185800451149971548 ≤
          ((S \ oldRadiusOwners6401 u0 u1 P S) \
            zeroExcessNewRadiusOwners6401 sigma u0 u1 S P).card ∧
        ∀ z ∈ (S \ oldRadiusOwners6401 u0 u1 P S) \
            zeroExcessNewRadiusOwners6401 sigma u0 u1 S P,
          keyFirstLaneRows6401 + 1 ≤
            (actualErrorSupportFullStack6401 sigma u0 u1 P z).rank) := by
  exact zeroExcessOrPositiveRank_sharpMassFork6401 sigma hfixed
    (frobeniusFixedScalars_card_le_q6401_of_pow sigma hsigma)
    u0 u1 S Aagree P hlarge hPdegree hrow howner

end BCHKSFrobeniusPrimitiveZeroIRS6401
end ProximityPrize.SubmissionLower
