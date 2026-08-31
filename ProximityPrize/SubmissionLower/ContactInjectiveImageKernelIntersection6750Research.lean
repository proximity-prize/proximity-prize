import ProximityPrize.Benchmark.TargetLower

 








namespace ProximityPrize.SubmissionLower.ContactInjectiveImageKernelIntersection6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u v w x

 
theorem exists_ne_zero_mem_kernel_of_finrank_lt
    {F : Type u} {V : Type v} {T : Type w}
    [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup T] [Module F T] [FiniteDimensional F T]
    (constraint : V →ₗ[F] T)
    (hfinrank : Module.finrank F T < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ constraint v = 0 := by
  have hker : LinearMap.ker constraint ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hfinrank
  obtain ⟨v, hvker, hvne⟩ := (Submodule.ne_bot_iff _).mp hker
  exact ⟨v, hvne, LinearMap.mem_ker.mp hvker⟩

 

theorem exists_ne_zero_image_mem_kernel_of_finrank_lt
    {F : Type u} {V : Type v} {A : Type w} {T : Type x}
    [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup A] [Module F A]
    [AddCommGroup T] [Module F T] [FiniteDimensional F T]
    (embed : V →ₗ[F] A) (constraint : A →ₗ[F] T)
    (hembed : Function.Injective embed)
    (hfinrank : Module.finrank F T < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ embed v ≠ 0 ∧ constraint (embed v) = 0 := by
  obtain ⟨v, hv, hzero⟩ :=
    exists_ne_zero_mem_kernel_of_finrank_lt (constraint.comp embed) hfinrank
  exact ⟨v, hv, fun hz => hv (hembed (by simpa only [map_zero] using hz)), hzero⟩

 

theorem exists_ne_zero_image_mem_kernel_of_rank_cap
    {F : Type u} {V : Type v} {A : Type w} {T : Type x}
    [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup A] [Module F A]
    [AddCommGroup T] [Module F T] [FiniteDimensional F T]
    (embed : V →ₗ[F] A) (constraint : A →ₗ[F] T)
    (hembed : Function.Injective embed) (rankCap : Nat)
    (htarget : Module.finrank F T ≤ rankCap)
    (hsource : rankCap < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ embed v ≠ 0 ∧ constraint (embed v) = 0 :=
  exists_ne_zero_image_mem_kernel_of_finrank_lt embed constraint hembed
    (htarget.trans_lt hsource)

section FixedMultiplication

variable {F : Type u} [Field F]
variable {A : Type v} [CommRing A] [IsDomain A] [Algebra F A]

 
def fixedLeftMultiplicationLinearMap (G : A) : A →ₗ[F] A where
  toFun Q := G * Q
  map_add' Q R := mul_add G Q R
  map_smul' c Q := by
    rw [mul_smul_comm]
    rfl

@[simp] theorem fixedLeftMultiplicationLinearMap_apply (G Q : A) :
    fixedLeftMultiplicationLinearMap (F := F) G Q = G * Q := rfl

 
theorem fixedLeftMultiplicationLinearMap_injective (G : A) (hG : G ≠ 0) :
    Function.Injective (fixedLeftMultiplicationLinearMap (F := F) G) := by
  intro Q R h
  exact mul_left_cancel₀ hG h

 
def fixedLeftMultiplicationFromSubmodule (G : A) (Low : Submodule F A) :
    Low →ₗ[F] A :=
  (fixedLeftMultiplicationLinearMap (F := F) G).comp Low.subtype

@[simp] theorem fixedLeftMultiplicationFromSubmodule_apply
    (G : A) (Low : Submodule F A) (Q : Low) :
    fixedLeftMultiplicationFromSubmodule G Low Q = G * (Q : A) := rfl

 
theorem fixedLeftMultiplicationFromSubmodule_injective
    (G : A) (hG : G ≠ 0) (Low : Submodule F A) :
    Function.Injective (fixedLeftMultiplicationFromSubmodule G Low) := by
  intro Q R h
  apply Subtype.ext
  exact mul_left_cancel₀ hG h

 
theorem exists_nonzero_fixed_product_in_kernel
    {T : Type w} [AddCommGroup T] [Module F T] [FiniteDimensional F T]
    (G : A) (hG : G ≠ 0) (Low : Submodule F A)
    [FiniteDimensional F Low] (constraint : A →ₗ[F] T)
    (hfinrank : Module.finrank F T < Module.finrank F Low) :
    ∃ Q : Low, Q ≠ 0 ∧ G * (Q : A) ≠ 0 ∧
      constraint (G * (Q : A)) = 0 := by
  simpa only [fixedLeftMultiplicationFromSubmodule_apply] using
    exists_ne_zero_image_mem_kernel_of_finrank_lt
      (fixedLeftMultiplicationFromSubmodule G Low) constraint
      (fixedLeftMultiplicationFromSubmodule_injective G hG Low) hfinrank

end FixedMultiplication

end


end ProximityPrize.SubmissionLower.ContactInjectiveImageKernelIntersection6750Research

#print axioms ProximityPrize.SubmissionLower.ContactInjectiveImageKernelIntersection6750Research.exists_ne_zero_image_mem_kernel_of_finrank_lt
#print axioms ProximityPrize.SubmissionLower.ContactInjectiveImageKernelIntersection6750Research.fixedLeftMultiplicationFromSubmodule_injective
#print axioms ProximityPrize.SubmissionLower.ContactInjectiveImageKernelIntersection6750Research.exists_nonzero_fixed_product_in_kernel
