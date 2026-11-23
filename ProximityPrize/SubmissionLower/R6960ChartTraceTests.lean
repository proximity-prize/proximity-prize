import ProximityPrize.SubmissionLower.R6960NormalizedFiber

noncomputable section
set_option Elab.async false
namespace Lower6960.ChartTraceTests

open Algebra Submodule

variable (A F E : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [Field F] [Algebra A F] [IsFractionRing A F] [Field E] [Algebra A E] [Algebra F E]
  [IsScalarTower A F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- A finite set of trace probes detects the normalized affine chart, even when no
polynomial basis for its integral closure has been chosen. -/
theorem integral_iff_finite_traces :
    ∃ probes : Finset E, ∀ x : E, IsIntegral A x ↔
      ∀ d ∈ probes, trace F E (x*d) ∈ (1 : Submodule A F) := by
  classical
  let S := (integralClosure A E).toSubmodule
  let D := (traceForm F E).dualSubmodule S
  obtain ⟨indices,b,bint⟩ := FiniteDimensional.exists_is_basis_integral A F E
  have bound : D ≤ span A (Set.range b.traceDual) := by
    rw [Module.Basis.traceDual_def, ← LinearMap.BilinForm.dualSubmodule_span_of_basis]
    have leS : span A (Set.range b) ≤ S := by
      apply span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact bint i
    intro d hd x hx
    exact hd x (leS hx)
  let := isNoetherian_span_of_finite A (Set.finite_range b.traceDual)
  have : IsNoetherian A D := isNoetherian_of_le bound
  have fg : D.FG := (Submodule.fg_top D).mp (IsNoetherian.noetherian _)
  obtain ⟨probes,gen⟩ := fg
  have oneD : (1:E) ∈ D := by
    intro x hx
    rw [traceForm_apply,one_mul]
    exact mem_one.mpr (IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_trace (show IsIntegral A x from hx)))
  refine ⟨probes,fun x => ⟨?_,?_⟩⟩
  · intro hx d hd
    have member : d ∈ D := gen ▸ subset_span hd
    simpa only [traceForm_apply,mul_comm d x] using member x hx
  · intro tested
    have all (d : E) (hd : d ∈ D) : trace F E (x*d) ∈ (1 : Submodule A F) := by
      rw [← gen] at hd
      have le : span A (probes : Set E) ≤ (1 : Submodule A F).comap
          (((traceForm F E) x).restrictScalars A) := span_le.mpr (fun z hz => tested z hz)
      exact le hd
    apply isIntegral_of_smul_mem_submodule D (fun h => one_ne_zero (show (1:E) ∈ (⊥ : Submodule A E) from h ▸ oneD))
      ⟨probes,gen⟩ x
    intro d hd s hs
    have ds : d*s ∈ D := by
      intro t ht
      simpa only [traceForm_apply,mul_assoc] using hd (s*t) (IsIntegral.mul hs ht)
    simpa only [smul_eq_mul,traceForm_apply,mul_assoc] using all (d*s) ds

#print axioms integral_iff_finite_traces
end Lower6960.ChartTraceTests
