/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Anne Baanen
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Norm_Basic
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Discriminant
section ProximityFlatProofPort
open Module
open scoped nonZeroDivisors
variable (R:Type*) {S:Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {Rₘ Sₘ:Type*} [CommRing Rₘ] [Algebra R Rₘ] [CommRing Sₘ] [Algebra S Sₘ]
variable (M:Submonoid R)
variable [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
variable [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
include M
open Algebra
theorem Algebra.map_leftMulMatrix_localization {ι:Type*} [Fintype ι] [DecidableEq ι]
    (b:Basis ι R S) (a:S):
    (algebraMap R Rₘ).mapMatrix (leftMulMatrix b a)=
    leftMulMatrix (b.localizationLocalization Rₘ M Sₘ) (algebraMap S Sₘ a):=by
  ext i j
  simp only [Matrix.map_apply,RingHom.mapMatrix_apply,leftMulMatrix_eq_repr_mul, ←map_mul,
    Basis.localizationLocalization_apply,Basis.localizationLocalization_repr_algebraMap]
theorem Algebra.norm_localization [Module.Free R S] [Module.Finite R S] (a:S):
    Algebra.norm Rₘ (algebraMap S Sₘ a)=algebraMap R Rₘ (Algebra.norm R a):=by
  cases subsingleton_or_nontrivial R
  · haveI:Subsingleton Rₘ:=Module.subsingleton R Rₘ
    simp [eq_iff_true_of_subsingleton]
  let b:=Module.Free.chooseBasis R S
  letI:=Classical.decEq (Module.Free.ChooseBasisIndex R S)
  rw [Algebra.norm_eq_matrix_det (b.localizationLocalization Rₘ M Sₘ),
    Algebra.norm_eq_matrix_det b,RingHom.map_det, ←Algebra.map_leftMulMatrix_localization]
variable {M} in
lemma Algebra.norm_eq_iff [Module.Free R S] [Module.Finite R S] {a:S} {b:R}
    (hM:M ≤ nonZeroDivisors R):Algebra.norm R a=b ↔
      (Algebra.norm Rₘ) ((algebraMap S Sₘ) a)=algebraMap R Rₘ b:=
  ⟨fun h↦h.symm ▸ Algebra.norm_localization _ M _,fun h↦
    IsLocalization.injective Rₘ hM <| h.symm ▸ (Algebra.norm_localization R M a).symm⟩
theorem Algebra.trace_localization [Module.Free R S] [Module.Finite R S] (a:S):
    Algebra.trace Rₘ Sₘ (algebraMap S Sₘ a)=algebraMap R Rₘ (Algebra.trace R S a):=by
  cases subsingleton_or_nontrivial R
  · haveI:Subsingleton Rₘ:=Module.subsingleton R Rₘ
    simp [eq_iff_true_of_subsingleton]
  let b:=Module.Free.chooseBasis R S
  letI:=Classical.decEq (Module.Free.ChooseBasisIndex R S)
  rw [Algebra.trace_eq_matrix_trace (b.localizationLocalization Rₘ M Sₘ),
    Algebra.trace_eq_matrix_trace b, ←Algebra.map_leftMulMatrix_localization]
  exact (AddMonoidHom.map_trace (algebraMap R Rₘ).toAddMonoidHom _).symm
section LocalizationLocalization
variable (Sₘ:Type*) [CommRing Sₘ] [Algebra S Sₘ] [Algebra Rₘ Sₘ] [Algebra R Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
theorem Algebra.traceMatrix_localizationLocalization (b:Basis ι R S):
    Algebra.traceMatrix Rₘ (b.localizationLocalization Rₘ M Sₘ)=
      (algebraMap R Rₘ).mapMatrix (Algebra.traceMatrix R b):=by
  have:Module.Finite R S:=Module.Finite.of_basis b
  have:Module.Free R S:=Module.Free.of_basis b
  ext i j:2
  simp_rw [RingHom.mapMatrix_apply,Matrix.map_apply,traceMatrix_apply,traceForm_apply,
    Basis.localizationLocalization_apply, ←map_mul]
  exact Algebra.trace_localization R M _
theorem Algebra.discr_localizationLocalization (b:Basis ι R S):
    Algebra.discr Rₘ (b.localizationLocalization Rₘ M Sₘ)=
    algebraMap R Rₘ (Algebra.discr R b):=by
  rw [Algebra.discr_def,Algebra.discr_def,RingHom.map_det,
    Algebra.traceMatrix_localizationLocalization]
end LocalizationLocalization
