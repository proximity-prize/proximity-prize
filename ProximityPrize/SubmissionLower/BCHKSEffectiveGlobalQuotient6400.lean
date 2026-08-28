import ProximityPrize.SubmissionLower.BCHKSEffectiveFixedRelation6400
import ProximityPrize.SubmissionLower.BCHKSGlobalQuotientDegree6400

/-! # Cancelling the inactive part of the fixed defect from the global quotient -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSEffectiveGlobalQuotient6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSGlobalInhomogeneousKeyEquation6400
open BCHKSMultiplierDefectAbstract6400
open BCHKSEffectiveFixedRelation6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The nodes in the original fixed container where the common global
quotient vanishes identically in the challenge. -/
noncomputable def score6400InactiveFixedDefect
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    Finset IRSProfile.Index :=
  Fixed \ score6400EffectiveFixedDefect Fixed K

/-- The inactive fixed-node locator, embedded as challenge-constant
coefficients. -/
noncomputable def score6400InactiveFixedLocatorLift
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    IRSProfile.Field[X][X] :=
  (outsideAgreementLocator IRSProfile.domain Fixed
      (score6400EffectiveFixedDefect Fixed K)).map
    (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X])

theorem score6400EffectiveFixedDefect_subset
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    score6400EffectiveFixedDefect Fixed K ⊆ Fixed := by
  intro i hi
  exact (mem_score6400EffectiveFixedDefect Fixed K i).mp hi |>.1

@[simp]
theorem score6400InactiveFixedLocatorLift_natDegree
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    (score6400InactiveFixedLocatorLift Fixed K).natDegree =
      (score6400InactiveFixedDefect Fixed K).card := by
  rw [score6400InactiveFixedLocatorLift,
    Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective,
    outsideAgreementLocator_natDegree]
  rfl

theorem score6400InactiveFixedLocatorLift_ne_zero
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    score6400InactiveFixedLocatorLift Fixed K ≠ 0 := by
  rw [score6400InactiveFixedLocatorLift]
  intro hzero
  apply outsideAgreementLocator_ne_zero IRSProfile.domain Fixed
    (score6400EffectiveFixedDefect Fixed K)
  apply Polynomial.map_injective
    (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X])
    Polynomial.C_injective
  simpa only [Polynomial.map_zero] using hzero

/-- Every inactive fixed node is a root of `K`, so its full nodal locator
divides `K` over the challenge polynomial coefficient ring. -/
theorem score6400InactiveFixedLocatorLift_dvd
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    score6400InactiveFixedLocatorLift Fixed K ∣ K := by
  apply mapped_outsideAgreementLocator_dvd IRSProfile.domain Fixed
    (score6400EffectiveFixedDefect Fixed K) K
  intro i hiFixed hiEffective
  exact score6400_globalQuotient_eval_zero_of_fixed_not_effective
    Fixed K i hiFixed hiEffective

/-- The global quotient after cancelling all challenge-identically-zero
fixed nodes. -/
noncomputable def score6400ReducedGlobalQuotient
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    IRSProfile.Field[X][X] :=
  Classical.choose (score6400InactiveFixedLocatorLift_dvd Fixed K)

theorem score6400InactiveFixedLocatorLift_mul_reducedGlobalQuotient
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    score6400InactiveFixedLocatorLift Fixed K *
        score6400ReducedGlobalQuotient Fixed K = K := by
  exact (Classical.choose_spec
    (score6400InactiveFixedLocatorLift_dvd Fixed K)).symm

/-- The two complement locators concatenate when the smaller defect is a
subset of the larger one. -/
theorem outsideAgreementLocator_univ_mul_fixed
    {F I : Type} [Field F] [Fintype I] [DecidableEq I]
    (alpha : I ↪ F) (Fixed Effective : Finset I)
    (hsubset : Effective ⊆ Fixed) :
    outsideAgreementLocator alpha Finset.univ Fixed *
        outsideAgreementLocator alpha Fixed Effective =
      outsideAgreementLocator alpha Finset.univ Effective := by
  classical
  simp only [outsideAgreementLocator, Lagrange.nodal]
  rw [← Finset.prod_union]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    constructor
    · rintro (hiFixed | ⟨hiFixed, hiEffective⟩)
      · exact fun hi ↦ hiFixed (hsubset hi)
      · exact hiEffective
    · intro hiEffective
      by_cases hiFixed : i ∈ Fixed
      · exact Or.inr ⟨hiFixed, hiEffective⟩
      · exact Or.inl hiFixed
  · rw [Finset.disjoint_left]
    intro i hiOutside hiInside
    exact (Finset.mem_sdiff.mp hiOutside).2
      (Finset.mem_sdiff.mp hiInside).1

/-- Mapped complement locators satisfy the same concatenation identity. -/
theorem score6400_mappedComplement_mul_inactive
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) *
        score6400InactiveFixedLocatorLift Fixed K =
      (outsideAgreementLocator IRSProfile.domain Finset.univ
          (score6400EffectiveFixedDefect Fixed K)).map
        (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) := by
  have hbase := outsideAgreementLocator_univ_mul_fixed
    IRSProfile.domain Fixed (score6400EffectiveFixedDefect Fixed K)
      (score6400EffectiveFixedDefect_subset Fixed K)
  have hmapped := congrArg
    (Polynomial.map
      (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X])) hbase
  simpa only [Polynomial.map_mul,
    score6400InactiveFixedLocatorLift] using hmapped

/-- Cancelling the inactive fixed-node locator rewrites the same global
residual with precisely the effective defect as its complement. -/
theorem score6400_reducedGlobalQuotient_factorization
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (Fixed : Finset IRSProfile.Index)
    (A B C K : IRSProfile.Field[X][X])
    (hglobal :
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
            (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C) :
    (outsideAgreementLocator IRSProfile.domain Finset.univ
        (score6400EffectiveFixedDefect Fixed K)).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) *
        score6400ReducedGlobalQuotient Fixed K =
      A * score6400ReceivedBivariate f₀ f₁ +
        B * score6400FrobeniusReceivedBivariate f₀ f₁ - C := by
  calc
    _ = ((outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
            (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) *
          score6400InactiveFixedLocatorLift Fixed K) *
        score6400ReducedGlobalQuotient Fixed K := by
          rw [score6400_mappedComplement_mul_inactive]
    _ = (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) *
        (score6400InactiveFixedLocatorLift Fixed K *
          score6400ReducedGlobalQuotient Fixed K) := by rw [mul_assoc]
    _ = (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K := by
          rw [score6400InactiveFixedLocatorLift_mul_reducedGlobalQuotient]
    _ = _ := hglobal

theorem score6400ReducedGlobalQuotient_ne_zero
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X])
    (hK : K ≠ 0) :
    score6400ReducedGlobalQuotient Fixed K ≠ 0 := by
  intro hzero
  apply hK
  rw [← score6400InactiveFixedLocatorLift_mul_reducedGlobalQuotient
    Fixed K, hzero, mul_zero]

/-- Cancelling the inactive locator subtracts exactly its node count from
the quotient degree. -/
theorem score6400ReducedGlobalQuotient_natDegree_lt_of_Kdegree
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X])
    (d : Nat) (hK : K ≠ 0)
    (hKdegree : K.natDegree < Fixed.card + d) :
    (score6400ReducedGlobalQuotient Fixed K).natDegree <
      (score6400EffectiveFixedDefect Fixed K).card + d := by
  have hReduced := score6400ReducedGlobalQuotient_ne_zero Fixed K hK
  have hdegree := congrArg Polynomial.natDegree
    (score6400InactiveFixedLocatorLift_mul_reducedGlobalQuotient Fixed K)
  rw [Polynomial.natDegree_mul
      (score6400InactiveFixedLocatorLift_ne_zero Fixed K) hReduced,
    score6400InactiveFixedLocatorLift_natDegree] at hdegree
  have hpartition := Finset.card_sdiff_add_card_inter Fixed
    (score6400EffectiveFixedDefect Fixed K)
  rw [Finset.inter_eq_right.mpr
    (score6400EffectiveFixedDefect_subset Fixed K)] at hpartition
  change (Fixed \ score6400EffectiveFixedDefect Fixed K).card +
      (score6400EffectiveFixedDefect Fixed K).card = Fixed.card at hpartition
  rw [← score6400InactiveFixedDefect] at hpartition
  omega

end BCHKSEffectiveGlobalQuotient6400
end ProximityPrize.SubmissionLower
