import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactKernelSelectedInterpolation6750Research
import ProximityPrize.SubmissionLower.ContactSelectedCount6750Research

 







namespace ProximityPrize.SubmissionLower
namespace ContactSelectedInterpolationProvider6750Research

open ProximityPrize.Benchmark
open ContactKernelSelectedInterpolation6750Research
open ContactSelectedCount6750Research

noncomputable section

set_option autoImplicit false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

 
def toSelectedInterpolants6750 {u0 u1 : I → K}
    (S : SelectedInterpolants6750Source u0 u1) :
    SelectedInterpolants6750 u0 u1 where
  QA := S.QA
  QB := S.QB
  QC := S.QC
  QA_ne_zero := S.QA_ne_zero
  QB_ne_zero := S.QB_ne_zero
  QC_ne_zero := S.QC_ne_zero
  QA_mem := S.QA_mem
  QB_mem := S.QB_mem
  QC_mem := S.QC_mem
  gcd12_mem := S.gcd12_mem
  oldCore_dvd_B := S.oldCore_dvd_B
  universal_cover := S.universal_cover

theorem exists_outer_selected_interpolants6750 (u0 u1 : I → K) :
    Nonempty (SelectedInterpolants6750 u0 u1) := by
  obtain ⟨S⟩ := exists_selected_interpolants u0 u1
  exact ⟨toSelectedInterpolants6750 S⟩

 
theorem closedSelectedInterpolantsProvider6750 :
    SelectedInterpolantsProvider6750 := by
  intro u0 u1
  exact exists_outer_selected_interpolants6750 u0 u1

end


end ContactSelectedInterpolationProvider6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactSelectedInterpolationProvider6750Research.closedSelectedInterpolantsProvider6750
