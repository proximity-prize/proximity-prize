import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSimultaneousOrdinaryUnion6750Research

 













namespace ProximityPrize.SubmissionLower.ContactFixedOrdinaryQuotientExistence6750Research

open scoped Classical
open ContactInterpolation

noncomputable section

set_option autoImplicit false

universe u v w

 

theorem exists_ne_zero_mem_inf_of_finrank_lt_add
    {F : Type u} {V : Type v}
    [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (A B : Submodule F V)
    (hdim : Module.finrank F V <
      Module.finrank F A + Module.finrank F B) :
    ∃ x : V, x ≠ 0 ∧ x ∈ A ∧ x ∈ B := by
  have hsup : Module.finrank F (A ⊔ B : Submodule F V) ≤
      Module.finrank F V := Submodule.finrank_le _
  have hformula := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hinf : 0 < Module.finrank F (A ⊓ B : Submodule F V) := by
    omega
  obtain ⟨x, hx⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := F)
      (M := (A ⊓ B : Submodule F V))).mp hinf
  refine ⟨x.1, ?_, x.2.1, x.2.2⟩
  intro hzero
  apply hx
  exact Subtype.ext hzero

 
theorem exists_ne_zero_mem_inf_of_quotient_finrank_add_lt
    {F : Type u} {V : Type v}
    [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (A B : Submodule F V)
    (hcodim : Module.finrank F (V ⧸ A) +
        Module.finrank F (V ⧸ B) < Module.finrank F V) :
    ∃ x : V, x ≠ 0 ∧ x ∈ A ∧ x ∈ B := by
  apply exists_ne_zero_mem_inf_of_finrank_lt_add A B
  have hA := Submodule.finrank_quotient_add_finrank A
  have hB := Submodule.finrank_quotient_add_finrank B
  omega

 


theorem exists_ne_zero_map_mem_of_quotient_finrank_lt
    {F : Type u} {V : Type v} {W : Type w}
    [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    [FiniteDimensional F V]
    (qLin : V →ₗ[F] W) (Low : Submodule F W)
    [FiniteDimensional F (W ⧸ Low)]
    (hcodim : Module.finrank F (W ⧸ Low) < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ qLin v ∈ Low := by
  let reduced : V →ₗ[F] (W ⧸ Low) := Low.mkQ.comp qLin
  have hker : LinearMap.ker reduced ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hcodim
  obtain ⟨v, hvker, hvne⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨v, hvne, ?_⟩
  have hzero : reduced v = 0 := (LinearMap.mem_ker.mp hvker)
  change Low.mkQ (qLin v) = 0 at hzero
  exact (Submodule.Quotient.mk_eq_zero Low).mp hzero

 

theorem exists_ne_zero_and_map_ne_zero_mem_of_quotient_finrank_lt
    {F : Type u} {V : Type v} {W : Type w}
    [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    [FiniteDimensional F V]
    (qLin : V →ₗ[F] W) (Low : Submodule F W)
    [FiniteDimensional F (W ⧸ Low)]
    (hinjective : Function.Injective qLin)
    (hcodim : Module.finrank F (W ⧸ Low) < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ qLin v ≠ 0 ∧ qLin v ∈ Low := by
  obtain ⟨v, hv, hvLow⟩ :=
    exists_ne_zero_map_mem_of_quotient_finrank_lt qLin Low hcodim
  refine ⟨v, hv, ?_, hvLow⟩
  intro hqzero
  apply hv
  apply hinjective
  simpa only [map_zero] using hqzero

 



abbrev lowInsideHigh
    {F : Type u} {W : Type w}
    [Field F] [AddCommGroup W] [Module F W]
    (High Low : Submodule F W) : Submodule F High :=
  Low.comap High.subtype

 


theorem exists_ne_zero_map_mem_low_of_nested_codim_lt
    {F : Type u} {V : Type v} {W : Type w}
    [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    [FiniteDimensional F V]
    (qLin : V →ₗ[F] W) (High Low : Submodule F W)
    [FiniteDimensional F (High ⧸ lowInsideHigh High Low)]
    (himage : ∀ v, qLin v ∈ High)
    (hinjective : Function.Injective qLin)
    (hcodim : Module.finrank F (High ⧸ lowInsideHigh High Low) <
      Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ qLin v ≠ 0 ∧ qLin v ∈ Low := by
  let qHigh : V →ₗ[F] High := LinearMap.codRestrict High qLin himage
  have hqHigh : Function.Injective qHigh := by
    intro x y hxy
    apply hinjective
    simpa [qHigh, LinearMap.codRestrict_apply] using congrArg Subtype.val hxy
  obtain ⟨v, hv, hqv, hlow⟩ :=
    exists_ne_zero_and_map_ne_zero_mem_of_quotient_finrank_lt
      qHigh (lowInsideHigh High Low) hqHigh hcodim
  have hqv' : qLin v ≠ 0 := by
    intro hzero
    apply hqv
    apply Subtype.ext
    simpa [qHigh, LinearMap.codRestrict_apply] using hzero
  have hlow' : qLin v ∈ Low := by
    simpa [lowInsideHigh, qHigh, LinearMap.codRestrict_apply] using hlow
  exact ⟨v, hv, hqv', hlow'⟩

 

theorem exists_ne_zero_map_mem_low_of_nested_codim_cap
    {F : Type u} {V : Type v} {W : Type w}
    [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    [FiniteDimensional F V]
    (qLin : V →ₗ[F] W) (High Low : Submodule F W)
    [FiniteDimensional F (High ⧸ lowInsideHigh High Low)]
    (himage : ∀ v, qLin v ∈ High)
    (hinjective : Function.Injective qLin)
    (codimCap : Nat)
    (hcodim : Module.finrank F (High ⧸ lowInsideHigh High Low) ≤ codimCap)
    (hsource : codimCap < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ qLin v ≠ 0 ∧ qLin v ∈ Low := by
  exact exists_ne_zero_map_mem_low_of_nested_codim_lt qLin High Low
    himage hinjective (hcodim.trans_lt hsource)

 

theorem globalCoefficientBox_mono_weighted
    {F : Type u} [Field F] {Dlow Dhigh w0 L s : Nat}
    (hD : Dlow ≤ Dhigh) :
    globalCoefficientBox F Dlow w0 L s ≤
      globalCoefficientBox F Dhigh w0 L s := by
  apply MvPolynomial.restrictSupport_mono
  intro d hd
  exact ⟨hd.1, hd.2.1, hd.2.2.trans_le hD⟩

 


theorem exists_fixed_nonzero_low_box_image_of_codim_cap
    {F : Type u} {V : Type v}
    [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Dhigh Dlow w0 L s : Nat)
    (qLin : V →ₗ[F] MvPolynomial (Fin 4) F)
    [FiniteDimensional F
      (globalCoefficientBox F Dhigh w0 L s ⧸
        lowInsideHigh (globalCoefficientBox F Dhigh w0 L s)
          (globalCoefficientBox F Dlow w0 L s))]
    (himage : ∀ v, qLin v ∈ globalCoefficientBox F Dhigh w0 L s)
    (hinjective : Function.Injective qLin)
    (codimCap : Nat)
    (hcodim : Module.finrank F
      (globalCoefficientBox F Dhigh w0 L s ⧸
        lowInsideHigh (globalCoefficientBox F Dhigh w0 L s)
          (globalCoefficientBox F Dlow w0 L s)) ≤ codimCap)
    (hsource : codimCap < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ qLin v ≠ 0 ∧
      qLin v ∈ globalCoefficientBox F Dlow w0 L s := by
  exact exists_ne_zero_map_mem_low_of_nested_codim_cap qLin
    (globalCoefficientBox F Dhigh w0 L s)
    (globalCoefficientBox F Dlow w0 L s) himage hinjective codimCap
    hcodim hsource

end

end ProximityPrize.SubmissionLower.ContactFixedOrdinaryQuotientExistence6750Research

#print axioms ProximityPrize.SubmissionLower.ContactFixedOrdinaryQuotientExistence6750Research.exists_ne_zero_mem_inf_of_finrank_lt_add
#print axioms ProximityPrize.SubmissionLower.ContactFixedOrdinaryQuotientExistence6750Research.exists_ne_zero_map_mem_of_quotient_finrank_lt
#print axioms ProximityPrize.SubmissionLower.ContactFixedOrdinaryQuotientExistence6750Research.exists_ne_zero_map_mem_low_of_nested_codim_cap
#print axioms ProximityPrize.SubmissionLower.ContactFixedOrdinaryQuotientExistence6750Research.exists_fixed_nonzero_low_box_image_of_codim_cap
