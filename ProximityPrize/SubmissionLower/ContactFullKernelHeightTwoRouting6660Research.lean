import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition
import ProximityPrize.SubmissionLower.ContactFullKernelHeightTwoIncidence6660Research
import ProximityPrize.SubmissionLower.ContactGeometricFirstTail

 






















namespace ProximityPrize.SubmissionLower
namespace ContactFullKernelHeightTwoRouting6660Research

open scoped Classical BigOperators
open ContactImplicitContactLift ContactSingularAuxiliary
open ContactSelectedSeedDecomposition ContactTranslation
open ContactGeometricFirstTail ContactGenericSurface ContactGaussLocalization

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

local instance : DecidableEq K := Classical.decEq K

def auxiliarySeeds
    (F0 : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (seeds : Finset K) : Finset K :=
  seeds.filter (fun gamma ↦
    specialization K (selected gamma) gamma (singularAuxiliary F0) = 0)

def regularFactorSeeds
    (F0 G : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (seeds : Finset K) : Finset K :=
  seeds.filter (fun gamma ↦ RegularSolution G (selected gamma) gamma)

theorem auxiliarySeeds_subset
    (F0 : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (seeds : Finset K) :
    auxiliarySeeds F0 selected seeds ⊆ seeds :=
  Finset.filter_subset _ _

theorem regularFactorSeeds_subset
    (F0 G : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (seeds : Finset K) :
    regularFactorSeeds F0 G selected seeds ⊆ seeds :=
  Finset.filter_subset _ _

 

theorem selected_seed_mem_auxiliary_or_regular_factor
    (F0 : MvPolynomial (Fin 4) K) (hF0 : F0 ≠ 0)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hsolution0 : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma F0 = 0)
    (gamma : K) (hgamma : gamma ∈ seeds) :
    gamma ∈ auxiliarySeeds F0 selected seeds ∨
      ∃ G ∈ positiveRFactors F0,
        gamma ∈ regularFactorSeeds F0 G selected seeds := by
  obtain haux | ⟨G, hG, hregular⟩ :=
    solution_regular_or_auxiliary F0 hF0 (selected gamma) gamma
      (hsolution0 gamma hgamma)
  · exact Or.inl (Finset.mem_filter.mpr ⟨hgamma, haux⟩)
  · exact Or.inr ⟨G, hG, Finset.mem_filter.mpr ⟨hgamma, hregular⟩⟩

 

theorem selected_card_le_auxiliary_add_regular_sum
    (F0 : MvPolynomial (Fin 4) K) (hF0 : F0 ≠ 0)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hsolution0 : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma F0 = 0) :
    seeds.card ≤ (auxiliarySeeds F0 selected seeds).card +
      ∑ G ∈ positiveRFactors F0,
        (regularFactorSeeds F0 G selected seeds).card := by
  classical
  let regularUnion := (positiveRFactors F0).biUnion
    (fun G ↦ regularFactorSeeds F0 G selected seeds)
  have hcover : seeds ⊆ auxiliarySeeds F0 selected seeds ∪ regularUnion := by
    intro gamma hgamma
    obtain haux | ⟨G, hG, hmem⟩ :=
      selected_seed_mem_auxiliary_or_regular_factor F0 hF0 selected seeds
        hsolution0 gamma hgamma
    · exact Finset.mem_union.mpr (Or.inl haux)
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_biUnion.mpr ⟨G, hG, hmem⟩))
  calc
    seeds.card ≤ (auxiliarySeeds F0 selected seeds ∪ regularUnion).card :=
      Finset.card_le_card hcover
    _ ≤ (auxiliarySeeds F0 selected seeds).card + regularUnion.card :=
      Finset.card_union_le _ _
    _ ≤ (auxiliarySeeds F0 selected seeds).card +
        ∑ G ∈ positiveRFactors F0,
          (regularFactorSeeds F0 G selected seeds).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _

 

def NoCommonNonunitDivisor
    (F0 F1 : MvPolynomial (Fin 4) K) : Prop :=
  ∀ G, G ∣ F0 → G ∣ F1 → IsUnit G

theorem positiveRFactor_not_dvd_second
    (F0 F1 G : MvPolynomial (Fin 4) K)
    (hcoprime : NoCommonNonunitDivisor F0 F1)
    (hG : G ∈ positiveRFactors F0) : ¬ G ∣ F1 := by
  intro hdiv1
  obtain ⟨hirred, hdiv0, _⟩ := positiveRFactors_spec F0 G hG
  exact hirred.not_isUnit (hcoprime G hdiv0 hdiv1)

 


theorem geometric_factor_not_dvd_second
    {L : Type*} [Field L] [Algebra (RationalCoefficients K) L]
    (F0 F1 G : MvPolynomial (Fin 4) K)
    (hcoprime : NoCommonNonunitDivisor F0 F1)
    (hG : G ∈ positiveRFactors F0)
    (g : MvPolynomial (Fin 3) L) (hg : Irreducible g)
    (hdivG : g ∣ geometricSurfaceMap K L G) :
    ¬ g ∣ geometricSurfaceMap K L F1 := by
  obtain ⟨hirred, _, hRpos⟩ := positiveRFactors_spec F0 G hG
  have hactive : 0 < G.degreeOf 1 + G.degreeOf 2 + G.degreeOf 3 := by
    omega
  intro hdiv1
  apply positiveRFactor_not_dvd_second F0 F1 G hcoprime hG
  exact (geometric_factor_dvd_iff K L G F1 hirred hactive g hg hdivG).mp hdiv1

 
theorem regularFactorSeeds_solve_second
    (F0 F1 G : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hsolution1 : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma F1 = 0) :
    ∀ gamma ∈ regularFactorSeeds F0 G selected seeds,
      specialization K (selected gamma) gamma F1 = 0 := by
  intro gamma hgamma
  exact hsolution1 gamma (regularFactorSeeds_subset F0 G selected seeds hgamma)

 


theorem selected_card_le_combined
    (F0 : MvPolynomial (Fin 4) K) (hF0 : F0 ≠ 0)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hsolution0 : ∀ gamma ∈ seeds,
      specialization K (selected gamma) gamma F0 = 0)
    (regularCeiling singularCeiling : ℕ)
    (hregular : (∑ G ∈ positiveRFactors F0,
      (regularFactorSeeds F0 G selected seeds).card) ≤ regularCeiling)
    (hsingular : (auxiliarySeeds F0 selected seeds).card ≤ singularCeiling) :
    seeds.card ≤ regularCeiling + singularCeiling := by
  exact (selected_card_le_auxiliary_add_regular_sum F0 hF0 selected seeds hsolution0).trans
    (Nat.add_le_add hsingular hregular |>.trans_eq (Nat.add_comm _ _))

def frozenRegularHeightTwoCeiling : ℕ := 2027023742225
def frozenSingularCeiling : ℕ := 18421197847852
def frozenCombinedHeightTwoCeiling : ℕ :=
  frozenRegularHeightTwoCeiling + frozenSingularCeiling
def fieldBudget : ℕ := 137490364055697543

theorem frozen_height_two_route_arithmetic :
    frozenCombinedHeightTwoCeiling = 20448221590077 ∧
      frozenCombinedHeightTwoCeiling < fieldBudget ∧
      fieldBudget - frozenCombinedHeightTwoCeiling = 137469915834107466 := by
  norm_num [frozenCombinedHeightTwoCeiling, frozenRegularHeightTwoCeiling,
    frozenSingularCeiling, fieldBudget]

end

end ContactFullKernelHeightTwoRouting6660Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactFullKernelHeightTwoRouting6660Research.selected_card_le_auxiliary_add_regular_sum
#print axioms ProximityPrize.SubmissionLower.ContactFullKernelHeightTwoRouting6660Research.positiveRFactor_not_dvd_second
#print axioms ProximityPrize.SubmissionLower.ContactFullKernelHeightTwoRouting6660Research.geometric_factor_not_dvd_second
#print axioms ProximityPrize.SubmissionLower.ContactFullKernelHeightTwoRouting6660Research.selected_card_le_combined
#print axioms ProximityPrize.SubmissionLower.ContactFullKernelHeightTwoRouting6660Research.frozen_height_two_route_arithmetic
