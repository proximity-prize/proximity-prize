import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFixedOrdinaryQuotientExistence6750Research
import ProximityPrize.SubmissionLower.ContactFixedFactorQuotientLinear6750Research
import ProximityPrize.SubmissionLower.ContactNestedFiveCapSlab6750Research

 









namespace ProximityPrize.SubmissionLower
namespace ContactNestedFiveCapQuotientIntersection6750Research

open scoped Classical BigOperators
open ContactFixedOrdinaryQuotientExistence6750Research
open ContactFixedFactorQuotientLinear6750Research
open ContactNestedFiveCapCoefficientBox6750Research
open ContactNestedFiveCapSlab6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 150000

universe u v

variable (F : Type u) [Field F]

 

 

theorem nestedFiveCap_lowInsideHigh_finrank_eq
    {Dlow Dhigh w T YS S : Nat} (hD : Dlow ≤ Dhigh) :
    Module.finrank F
        (lowInsideHigh
          (nestedFiveCapCoefficientBox F Dhigh w T YS S)
          (nestedFiveCapCoefficientBox F Dlow w T YS S)) =
      Module.finrank F
        (nestedFiveCapCoefficientBox F Dlow w T YS S) := by
  let High := nestedFiveCapCoefficientBox F Dhigh w T YS S
  let Low := nestedFiveCapCoefficientBox F Dlow w T YS S
  have hle : Low ≤ High := nestedFiveCapCoefficientBox_mono_D F hD
  calc
    Module.finrank F (lowInsideHigh High Low) =
        Module.finrank F ((lowInsideHigh High Low).map High.subtype) :=
      (Submodule.equivSubtypeMap High
        (lowInsideHigh High Low)).finrank_eq
    _ = Module.finrank F Low := by
      rw [lowInsideHigh, Submodule.map_comap_subtype]
      exact congrArg
        (fun U : Submodule F (MvPolynomial (Fin 4) F) ↦
          Module.finrank F U)
        (inf_eq_right.mpr hle)

 
theorem nestedFiveCap_quotient_finrank_eq_count_sub
    {Dlow Dhigh w T YS S : Nat} (hD : Dlow ≤ Dhigh) :
    Module.finrank F
        (nestedFiveCapCoefficientBox F Dhigh w T YS S ⧸
          lowInsideHigh
            (nestedFiveCapCoefficientBox F Dhigh w T YS S)
            (nestedFiveCapCoefficientBox F Dlow w T YS S)) =
      nestedFiveCapCoefficientCount Dhigh w T YS S -
        nestedFiveCapCoefficientCount Dlow w T YS S := by
  letI : FiniteDimensional F
      (nestedFiveCapCoefficientBox F Dhigh w T YS S) :=
    nestedFiveCapCoefficientBox_finiteDimensional F Dhigh w T YS S
  rw [Submodule.finrank_quotient]
  rw [nestedFiveCapCoefficientBox_finrank_eq_count]
  rw [nestedFiveCap_lowInsideHigh_finrank_eq F hD]
  rw [nestedFiveCapCoefficientBox_finrank_eq_count]

 

 


theorem exists_nonzero_image_mem_low_nestedFiveCap
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Dhigh Dlow w T YS S : Nat) (hD : Dlow ≤ Dhigh)
    (qLin : V →ₗ[F] MvPolynomial (Fin 4) F)
    (himage : ∀ v, qLin v ∈
      nestedFiveCapCoefficientBox F Dhigh w T YS S)
    (hinjective : Function.Injective qLin)
    (hsource : (Dhigh - Dlow) * nestedFiveCapChannelCount T YS S <
      Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ qLin v ≠ 0 ∧
      qLin v ∈ nestedFiveCapCoefficientBox F Dlow w T YS S := by
  let High := nestedFiveCapCoefficientBox F Dhigh w T YS S
  let Low := nestedFiveCapCoefficientBox F Dlow w T YS S
  letI : FiniteDimensional F High :=
    nestedFiveCapCoefficientBox_finiteDimensional F Dhigh w T YS S
  apply exists_ne_zero_map_mem_low_of_nested_codim_cap
    qLin High Low himage hinjective
      ((Dhigh - Dlow) * nestedFiveCapChannelCount T YS S)
  · rw [nestedFiveCap_quotient_finrank_eq_count_sub F hD]
    exact nestedFiveCapCoefficientCount_sub_le_slab hD
  · exact hsource

 

 






theorem exists_nonzero_mappedFixedFactorQuotient_mem_low_nestedFiveCap
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (H : MvPolynomial (Fin 4) F) (hH : H ≠ 0)
    (recon : V →ₗ[F] MvPolynomial (Fin 4) F)
    (hrecon : Function.Injective recon)
    (hdiv : ∀ v : V, H ∣ recon v)
    (Dhigh Dlow w T YS S : Nat) (hD : Dlow ≤ Dhigh)
    (himage : ∀ v,
      mappedFixedFactorQuotientLinearMap H hH recon hdiv v ∈
        nestedFiveCapCoefficientBox F Dhigh w T YS S)
    (hsource : (Dhigh - Dlow) * nestedFiveCapChannelCount T YS S <
      Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧
      mappedFixedFactorQuotientLinearMap H hH recon hdiv v ≠ 0 ∧
      mappedFixedFactorQuotientLinearMap H hH recon hdiv v ∈
        nestedFiveCapCoefficientBox F Dlow w T YS S ∧
      H * mappedFixedFactorQuotientLinearMap H hH recon hdiv v = recon v := by
  let qLin : V →ₗ[F] MvPolynomial (Fin 4) F :=
    mappedFixedFactorQuotientLinearMap H hH recon hdiv
  have hqinj : Function.Injective qLin :=
    mappedFixedFactorQuotientLinearMap_injective H hH recon hdiv hrecon
  obtain ⟨v, hv, hqv, hlow⟩ :=
    exists_nonzero_image_mem_low_nestedFiveCap F
      Dhigh Dlow w T YS S hD qLin himage hqinj hsource
  refine ⟨v, hv, hqv, hlow, ?_⟩
  exact mul_mappedFixedFactorQuotientLinearMap H hH recon hdiv v

end

end ContactNestedFiveCapQuotientIntersection6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapQuotientIntersection6750Research.nestedFiveCap_quotient_finrank_eq_count_sub
#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapQuotientIntersection6750Research.exists_nonzero_image_mem_low_nestedFiveCap
#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapQuotientIntersection6750Research.exists_nonzero_mappedFixedFactorQuotient_mem_low_nestedFiveCap
