import ProximityPrize.SubmissionLower.BCHKSReedSolomonSyndrome6400
import ProximityPrize.SubmissionLower.BCHKSExactSparsification6400

/-!
# Sparse MCA witnesses as Reed--Solomon locator data

This module adapts the exact sparsification predicates to the locator
syndrome theorem.  It also isolates the cancellation slopes at which the
affine error word vanishes at a point of the joint support.  Those slopes
must be paid for separately: their mixed matrix can be singular for the
unhelpful reason that it has a zero row.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open BCHKSExactSparsification6400

variable {F D : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype D] [DecidableEq D]

theorem pairSupport_values_eq_zero_of_not_mem
    (e₀ e₁ : D → F) {i : D} (hi : i ∉ pairSupport e₀ e₁) :
    e₀ i = 0 ∧ e₁ i = 0 := by
  simp only [pairSupport, wordSupport, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and, not_or, not_ne_iff] at hi
  exact hi

/-- Slopes at which the affine error word cancels at a coordinate of `T`.
Coordinates with zero second component contribute no slope. -/
def cancellationSlopes (e₀ e₁ : D → F) (T : Finset D) : Finset F :=
  (T.filter fun i => e₁ i ≠ 0).image fun i => -e₀ i / e₁ i

theorem mem_cancellationSlopes_iff
    (e₀ e₁ : D → F) (T : Finset D) (hT : T ⊆ pairSupport e₀ e₁)
    (z : F) :
    z ∈ cancellationSlopes e₀ e₁ T ↔
      ∃ i ∈ T, e₀ i + z * e₁ i = 0 := by
  constructor
  · intro hz
    rw [cancellationSlopes, Finset.mem_image] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    have hi₁ : e₁ i ≠ 0 := (Finset.mem_filter.mp hi).2
    refine ⟨i, (Finset.mem_filter.mp hi).1, ?_⟩
    field_simp
    ring
  · rintro ⟨i, hiT, hzero⟩
    have hiPair := hT hiT
    have hiEither : e₀ i ≠ 0 ∨ e₁ i ≠ 0 := by
      simpa only [pairSupport, wordSupport, Finset.mem_union,
        Finset.mem_filter, Finset.mem_univ, true_and] using hiPair
    have hi₁ : e₁ i ≠ 0 := by
      intro hi₁zero
      rw [hi₁zero, mul_zero, add_zero] at hzero
      exact hiEither.elim (fun hi₀ => hi₀ hzero) (fun h => h hi₁zero)
    rw [cancellationSlopes, Finset.mem_image]
    refine ⟨i, Finset.mem_filter.mpr ⟨hiT, hi₁⟩, ?_⟩
    symm
    apply (eq_div_iff hi₁).2
    linear_combination hzero

theorem card_cancellationSlopes_le
    (e₀ e₁ : D → F) (T : Finset D) :
    (cancellationSlopes e₀ e₁ T).card ≤ T.card := by
  calc
    (cancellationSlopes e₀ e₁ T).card ≤
        (T.filter fun i => e₁ i ≠ 0).card := by
      exact Finset.card_image_le
    _ ≤ T.card := Finset.card_filter_le _ _

theorem affine_error_ne_zero_on_support_of_not_cancellation
    (e₀ e₁ : D → F) (T : Finset D) (hT : T ⊆ pairSupport e₀ e₁)
    (z : F) (hz : z ∉ cancellationSlopes e₀ e₁ T) :
    ∀ i ∈ T, e₀ i + z * e₁ i ≠ 0 := by
  intro i hi hzero
  exact hz ((mem_cancellationSlopes_iff e₀ e₁ T hT z).2
    ⟨i, hi, hzero⟩)

/-- Unpack an MCA-bad witness for a Reed--Solomon code into an agreeing
polynomial and prove that its chosen agreement set meets the joint sparse
support. -/
theorem exists_rs_polynomial_data_of_mcaBad
    (α : D ↪ F) (k a : ℕ) (e₀ e₁ : D → F) (z : F)
    (hbad : MCABad (ReedSolomon.code α k) e₀ e₁ a z) :
    ∃ A : Finset D, ∃ P : F[X],
      a ≤ A.card ∧ P.degree < (k : WithBot ℕ) ∧
      (∀ i ∈ A, P.eval (α i) = e₀ i + z * e₁ i) ∧
      ∃ i, i ∈ A ∧ i ∈ pairSupport e₀ e₁ := by
  classical
  rcases hbad with ⟨A, hA, ⟨c, hc, hcAgree⟩, hpair⟩
  change c ∈ ReedSolomon.code α k at hc
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hc
  obtain ⟨P, hPdegree, rfl⟩ := hc
  have hPagree : ∀ i ∈ A, P.eval (α i) = e₀ i + z * e₁ i := by
    intro i hi
    simpa [ReedSolomon.evalOnPoints] using hcAgree i hi
  have hintersects : ∃ i, i ∈ A ∧ i ∈ pairSupport e₀ e₁ := by
    by_contra hnone
    push Not at hnone
    apply hpair
    refine ⟨0, (ReedSolomon.code α k).zero_mem,
      0, (ReedSolomon.code α k).zero_mem, ?_, ?_⟩
    · intro i hi
      have hz := (pairSupport_values_eq_zero_of_not_mem e₀ e₁
        (hnone i hi)).1
      simpa only [Pi.zero_apply] using hz.symm
    · intro i hi
      have hz := (pairSupport_values_eq_zero_of_not_mem e₀ e₁
        (hnone i hi)).2
      simpa only [Pi.zero_apply] using hz.symm
  exact ⟨A, P, hA, hPdegree, hPagree, hintersects⟩

open ProximityPrize.Benchmark

local instance koalaSexticChar :
    CharP IRSProfile.Field 2130706433 :=
  charP_of_injective_algebraMap' KoalaBear.Field 2130706433

local instance koalaPrimeFact : Fact (Nat.Prime 2130706433) :=
  ⟨by simpa [KoalaBear.fieldSize] using KoalaBear.is_prime⟩

/-- The characteristic Frobenius on the production sextic field. -/
noncomputable def koalaSexticFrobenius :
    IRSProfile.Field ≃+* IRSProfile.Field :=
  frobeniusEquiv IRSProfile.Field 2130706433

theorem koalaSexticFrobenius_fixed_domain (i : IRSProfile.Index) :
    koalaSexticFrobenius (IRSProfile.domain i) = IRSProfile.domain i := by
  rw [koalaSexticFrobenius, frobeniusEquiv_def]
  change (CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node i) :
      IRSProfile.Field) ^ 2130706433 =
    CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node i)
  calc
    (CompPoly.Extension.Ext.ofBase (IRSProfile.baseNttDomain.node i) :
        IRSProfile.Field) ^ 2130706433 =
        algebraMap KoalaBear.Field IRSProfile.Field
          (IRSProfile.baseNttDomain.node i ^ 2130706433) := by
      rw [map_pow]
      rfl
    _ = algebraMap KoalaBear.Field IRSProfile.Field
        (IRSProfile.baseNttDomain.node i) := by
      apply congrArg (algebraMap KoalaBear.Field IRSProfile.Field)
      simpa [KoalaBear.fieldSize] using ZMod.pow_card
        (IRSProfile.baseNttDomain.node i)
    _ = CompPoly.Extension.Ext.ofBase
        (IRSProfile.baseNttDomain.node i) := rfl

/-- Extend an affine error word from the production evaluation domain to the
whole field.  Only its values on the injective domain image are used. -/
noncomputable def score6400AffineErrorSource
    (e₀ e₁ : IRSProfile.Index → IRSProfile.Field) (z : IRSProfile.Field) :
    IRSProfile.Field → IRSProfile.Field :=
  Function.extend IRSProfile.domain (fun i => e₀ i + z * e₁ i) 0

@[simp]
theorem score6400AffineErrorSource_domain
    (e₀ e₁ : IRSProfile.Index → IRSProfile.Field) (z : IRSProfile.Field)
    (i : IRSProfile.Index) :
    score6400AffineErrorSource e₀ e₁ z (IRSProfile.domain i) =
      e₀ i + z * e₁ i := by
  exact IRSProfile.domain.injective.extend_apply _ _ i

/-- At the score-64 endpoint, a noncancelling sparse MCA witness in the
large-support branch produces all concrete data needed at the mixed-stack
interface. -/
theorem exists_score6400_mixed_witness_of_sparse_mcaBad
    (e₀ e₁ : IRSProfile.Index → IRSProfile.Field) (z : IRSProfile.Field)
    (hsparse : SparseAt e₀ e₁ 185364)
    (hbad : MCABad IRSProfile.baseCode e₀ e₁ 185364 z)
    (hnoncancel : z ∉ cancellationSlopes e₀ e₁ (pairSupport e₀ e₁))
    (hlarge : 54292 < (pairSupport e₀ e₁).card) :
    ∃ A : Finset IRSProfile.Index, ∃ P : IRSProfile.Field[X],
      185364 ≤ A.card ∧ P.natDegree ≤ 131071 ∧
      (∀ i ∈ A,
        P.eval (IRSProfile.domain i) = e₀ i + z * e₁ i) ∧
      (∃ i, i ∈ A ∧ i ∈ pairSupport e₀ e₁) ∧
      LinearMap.ker
        (mixedStackMatrix
          ((pairSupport e₀ e₁).map IRSProfile.domain)
          (score6400AffineErrorSource e₀ e₁ z)
          (fun x => koalaSexticFrobenius
            (score6400AffineErrorSource e₀ e₁ z x))
          54292 ((pairSupport e₀ e₁).card - 54292)).transpose.mulVecLin ≠ ⊥ ∧
      (∀ x ∈ (pairSupport e₀ e₁).map IRSProfile.domain,
        score6400AffineErrorSource e₀ e₁ z x ≠ 0) ∧
      54292 + ((pairSupport e₀ e₁).card - 54292) =
        (pairSupport e₀ e₁).card ∧
      (pairSupport e₀ e₁).card - 54292 ≤ 22488 := by
  classical
  have hbadRS : MCABad
      (ReedSolomon.code IRSProfile.domain IRSProfile.baseDimension)
      e₀ e₁ 185364 z := by
    simpa only [IRSProfile.baseCode] using hbad
  obtain ⟨A, P, hA, hPdegree, hPagree, hintersects⟩ :=
    exists_rs_polynomial_data_of_mcaBad
      IRSProfile.domain IRSProfile.baseDimension 185364 e₀ e₁ z hbadRS
  have hTcap : (pairSupport e₀ e₁).card ≤ 76780 := by
    change (pairSupport e₀ e₁).card ≤
      Fintype.card IRSProfile.Index - 185364 at hsparse
    norm_num [IRSProfile.Index] at hsparse
    exact hsparse
  have hPnat : P.natDegree ≤ 131071 := by
    by_cases hPzero : P = 0
    · simp [hPzero]
    · have hlt : P.natDegree < IRSProfile.baseDimension :=
        (Polynomial.natDegree_lt_iff_degree_lt hPzero).2 hPdegree
      norm_num [IRSProfile.baseDimension] at hlt ⊢
      omega
  have hAcap : (Finset.univ \ A).card ≤ 76780 := by
    calc
      (Finset.univ \ A).card =
          Fintype.card IRSProfile.Index - A.card := by
        rw [Finset.card_sdiff]
        simp
      _ ≤ Fintype.card IRSProfile.Index - 185364 :=
        Nat.sub_le_sub_left hA _
      _ = 76780 := by norm_num [IRSProfile.Index]
  have hdegreeRoom :
      (Finset.univ \ A).card + P.natDegree + 54292 ≤
        Fintype.card IRSProfile.Index - 1 := by
    norm_num [IRSProfile.Index]
    omega
  let e : IRSProfile.Index → IRSProfile.Field := fun i => e₀ i + z * e₁ i
  have hesupport : ∀ i ∉ pairSupport e₀ e₁, e i = 0 := by
    intro i hi
    obtain ⟨hi₀, hi₁⟩ := pairSupport_values_eq_zero_of_not_mem e₀ e₁ hi
    simp only [e, hi₀, hi₁, mul_zero, add_zero]
  have hesource : ∀ i ∈ pairSupport e₀ e₁,
      score6400AffineErrorSource e₀ e₁ z (IRSProfile.domain i) = e i := by
    intro i hi
    simp only [score6400AffineErrorSource_domain, e]
  have hhcap : (pairSupport e₀ e₁).card - 54292 ≤ 22488 := by omega
  have hhc : (pairSupport e₀ e₁).card - 54292 ≤ 54292 := by omega
  have htranspose : LinearMap.ker
      (mixedStackMatrix
        ((pairSupport e₀ e₁).map IRSProfile.domain)
        (score6400AffineErrorSource e₀ e₁ z)
        (fun x => koalaSexticFrobenius
          (score6400AffineErrorSource e₀ e₁ z x))
        54292 ((pairSupport e₀ e₁).card - 54292)).transpose.mulVecLin ≠ ⊥ := by
    apply mixedStack_transpose_ker_ne_bot_of_rs_locator
      IRSProfile.domain koalaSexticFrobenius
      koalaSexticFrobenius_fixed_domain A (pairSupport e₀ e₁) e
      (score6400AffineErrorSource e₀ e₁ z) P hesupport hesource
      hPagree hintersects 54292 ((pairSupport e₀ e₁).card - 54292)
      hhc hdegreeRoom
  have hsourceNe : ∀ x ∈ (pairSupport e₀ e₁).map IRSProfile.domain,
      score6400AffineErrorSource e₀ e₁ z x ≠ 0 := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp hx
    rw [← hix, score6400AffineErrorSource_domain]
    exact affine_error_ne_zero_on_support_of_not_cancellation
      e₀ e₁ (pairSupport e₀ e₁) (fun _ h => h) z hnoncancel i hi
  refine ⟨A, P, hA, hPnat, hPagree, hintersects, htranspose,
    hsourceNe, ?_, hhcap⟩
  omega

end ProximityPrize.SubmissionLower
