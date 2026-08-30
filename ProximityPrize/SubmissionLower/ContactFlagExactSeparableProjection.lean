import ProximityPrize.SubmissionLower.GlobalSeparableShear
import ProximityPrize.SubmissionLower.ContactLeadingCancellation
import ProximityPrize.SubmissionLower.ContactSparsePoleZeroCount
import ProximityPrize.SubmissionLower.ContactResidualSparseComponentAdapter
import ProximityPrize.SubmissionLower.ContactFlagAffineFamilyDegree
import ProximityPrize.SubmissionLower.ContactFlagPoleInequality
namespace ProximityPrize.SubmissionLower.ContactFlagExactSeparableProjection

open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential IsDedekindDomain
open ArbitraryRationalProjection GlobalSeparableShear
open CoordinateBoxZeroCount ContactSparsePoleSupport
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveZeroCount
open ContactRegularComponentCover
open ContactFlagAffineFamilyDegree

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000

theorem exists_nonzero_avoiding_finite_subsingleton
    {K ι : Type*} [Field K] [Infinite K] [Finite ι]
    (Bad : ι → K → Prop)
    (hsingle : ∀ i {a b}, Bad i a → Bad i b → a = b) :
    ∃ a : K, a ≠ 0 ∧ ∀ i, ¬ Bad i a := by
  classical
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := Fintype.ofFinite ι
  let representative : ι → K := fun i ↦
    if h : ∃ a, Bad i a then Classical.choose h else 0
  let forbidden : Finset K := Finset.univ.image representative
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset (insert 0 forbidden)
  refine ⟨a, ?_, ?_⟩
  · intro hzero
    exact ha (hzero ▸ Finset.mem_insert_self 0 forbidden)
  · intro i hbad
    have hex : ∃ b, Bad i b := ⟨a, hbad⟩
    have hrepbad : Bad i (representative i) := by
      simp only [representative, dif_pos hex]
      exact Classical.choose_spec hex
    have hab : a = representative i := hsingle i hbad hrepbad
    have hmem : representative i ∈ forbidden := by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    exact ha (Finset.mem_insert_of_mem (hab ▸ hmem))

theorem valuation_shear_bad_coefficient_subsingleton
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : CoordinatePlaceClassification.NormalizedValuation K L)
    (r z : L) :
    ∀ {a b : K},
      v.val (r + a • z) < max (v.val r) (v.val z) →
      v.val (r + b • z) < max (v.val r) (v.val z) → a = b := by
  intro a b ha hb
  by_contra hab
  have hab0 : a - b ≠ 0 := sub_ne_zero.mpr hab
  letI : v.val.IsTrivialOn K := v.property.2
  have hdiff : v.val ((r + a • z) - (r + b • z)) <
      max (v.val r) (v.val z) := v.val.map_sub_lt ha hb
  have hvaldiff : v.val ((r + a • z) - (r + b • z)) = v.val z := by
    rw [show (r + a • z) - (r + b • z) = (a - b) • z by module,
      Algebra.smul_def, map_mul,
      Valuation.IsTrivialOn.eq_one (a - b) hab0, one_mul]
  rw [hvaldiff] at hdiff
  have hzr : v.val z < v.val r := by
    simpa only [lt_max_iff, lt_self_iff_false, or_false] using hdiff
  have hmax : max (v.val r) (v.val z) = v.val r := max_eq_left hzr.le
  have ha0 : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_smul, add_zero, hmax] at ha
    exact (lt_irrefl _ ha).elim
  have haz : v.val (a • z) = v.val z := by
    rw [Algebra.smul_def, map_mul,
      Valuation.IsTrivialOn.eq_one a ha0, one_mul]
  have hsum : v.val (r + a • z) = v.val r := by
    apply v.val.map_add_eq_of_lt_left
    rwa [haz]
  rw [hsum, hmax] at ha
  exact (lt_irrefl _ ha).elim

section FiniteFamily

variable {K : Type*} [Field K] [IsAlgClosed K]
variable {I : Type*} [Fintype I]
variable (E : I → Type*) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
variable (r z : ∀ i, E i)
variable (W : ∀ i,
  Finset (CoordinatePlaceClassification.NormalizedValuation K (E i)))

end FiniteFamily

section RegularComponents

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
variable {G T H : MvPolynomial (Fin 3) Ω}

end RegularComponents

end

end ProximityPrize.SubmissionLower.ContactFlagExactSeparableProjection
