import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSecondContactKernel6660Research

 









namespace ProximityPrize.SubmissionLower.ContactSecondContactKernelSections6660Research

open ProximityPrize.Benchmark
open ContactSecondContactSFreeInterpolation6660Research
open ContactSecondContactUVSpan6660Research
open ContactSecondContactConstraintMap6660Research
open ContactSecondContactKernel6660Research

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.checkUnivs false

noncomputable section

variable (K : Type*) [Field K]

 


theorem globalConstraint_kernel_finrank_ge {I : Type*} [Fintype I]
    (D w C rCap m : ℕ) (nodes u0 u1 : I → K) :
    coefficientCount D w C rCap -
        Fintype.card I * localUVRankBound m C rCap ≤
      Module.finrank K (LinearMap.ker
        (globalConstraint K D w C rCap m nodes u0 u1)) := by
  classical
  letI : Module.Finite K (uvSpan K m C rCap) :=
    FiniteDimensional.span_of_finite K
      (Set.finite_range (uvSpanVector K m C rCap))
  have hrange : Module.finrank K (LinearMap.range
      (globalConstraint K D w C rCap m nodes u0 u1)) ≤
      Fintype.card I * localUVRankBound m C rCap := by
    calc
      Module.finrank K (LinearMap.range
          (globalConstraint K D w C rCap m nodes u0 u1)) ≤
          Module.finrank K (GlobalTarget K I m C rCap) :=
        Submodule.finrank_le _
      _ ≤ Fintype.card I * localUVRankBound m C rCap :=
        globalTarget_finrank_le K m C rCap
  have hsum :=
    (globalConstraint K D w C rCap m nodes u0 u1).finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card, coefficient_index_card] at hsum
  apply Nat.sub_le_iff_le_add.mpr
  omega

 

theorem row6660_globalConstraint_kernel_finrank_ge
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1115960 ≤ Module.finrank IRSProfile.Field (LinearMap.ker
      (globalConstraint IRSProfile.Field 5848704 131071 717 9 32
        (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1)) := by
  have hcard : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  have h := globalConstraint_kernel_finrank_ge IRSProfile.Field
    5848704 131071 717 9 32
    (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1
  rw [hcard, row6660_coefficient_count_exact,
    row6660_local_uv_rank_exact] at h
  norm_num at h ⊢
  exact h

 

theorem exists_row6660_three_independent_kernel_rows
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ rows : Fin 3 → LinearMap.ker
        (globalConstraint IRSProfile.Field 5848704 131071 717 9 32
          (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1),
      LinearIndependent IRSProfile.Field rows := by
  apply exists_linearIndependent_of_le_finrank
  exact (show 3 ≤ 1115960 by norm_num).trans
    (row6660_globalConstraint_kernel_finrank_ge u0 u1)

end

end ProximityPrize.SubmissionLower.ContactSecondContactKernelSections6660Research

#print axioms ProximityPrize.SubmissionLower.ContactSecondContactKernelSections6660Research.globalConstraint_kernel_finrank_ge
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactKernelSections6660Research.row6660_globalConstraint_kernel_finrank_ge
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactKernelSections6660Research.exists_row6660_three_independent_kernel_rows
