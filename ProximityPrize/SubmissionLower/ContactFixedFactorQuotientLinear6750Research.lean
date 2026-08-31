import ProximityPrize.Benchmark.TargetLower

 








namespace ProximityPrize.SubmissionLower.ContactFixedFactorQuotientLinear6750Research

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

universe u v

variable {F : Type u} [Field F]
variable {A : Type v} [CommRing A] [IsDomain A] [Algebra F A]

 

def fixedFactorQuotient (G : A) (V : Submodule F A)
    (hdiv : ∀ v : V, G ∣ (v : A)) (v : V) : A :=
  Classical.choose (hdiv v)

 
theorem mul_fixedFactorQuotient (G : A) (V : Submodule F A)
    (hdiv : ∀ v : V, G ∣ (v : A)) (v : V) :
    G * fixedFactorQuotient G V hdiv v = (v : A) := by
  simpa only [fixedFactorQuotient] using (Classical.choose_spec (hdiv v)).symm

 

theorem fixedFactorQuotient_add (G : A) (hG : G ≠ 0)
    (V : Submodule F A) (hdiv : ∀ v : V, G ∣ (v : A)) (v w : V) :
    fixedFactorQuotient G V hdiv (v + w) =
      fixedFactorQuotient G V hdiv v + fixedFactorQuotient G V hdiv w := by
  apply mul_left_cancel₀ hG
  rw [mul_fixedFactorQuotient, mul_add, mul_fixedFactorQuotient,
    mul_fixedFactorQuotient]
  rfl

 
theorem fixedFactorQuotient_smul (G : A) (hG : G ≠ 0)
    (V : Submodule F A) (hdiv : ∀ v : V, G ∣ (v : A)) (c : F) (v : V) :
    fixedFactorQuotient G V hdiv (c • v) =
      c • fixedFactorQuotient G V hdiv v := by
  apply mul_left_cancel₀ hG
  rw [mul_fixedFactorQuotient, mul_smul_comm, mul_fixedFactorQuotient]
  rfl

 
def fixedFactorQuotientLinearMap (G : A) (hG : G ≠ 0)
    (V : Submodule F A) (hdiv : ∀ v : V, G ∣ (v : A)) : V →ₗ[F] A where
  toFun := fixedFactorQuotient G V hdiv
  map_add' := fixedFactorQuotient_add G hG V hdiv
  map_smul' := fixedFactorQuotient_smul G hG V hdiv

@[simp] theorem fixedFactorQuotientLinearMap_apply
    (G : A) (hG : G ≠ 0) (V : Submodule F A)
    (hdiv : ∀ v : V, G ∣ (v : A)) (v : V) :
    fixedFactorQuotientLinearMap G hG V hdiv v =
      fixedFactorQuotient G V hdiv v := rfl

 
theorem mul_fixedFactorQuotientLinearMap
    (G : A) (hG : G ≠ 0) (V : Submodule F A)
    (hdiv : ∀ v : V, G ∣ (v : A)) (v : V) :
    G * fixedFactorQuotientLinearMap G hG V hdiv v = (v : A) :=
  mul_fixedFactorQuotient G V hdiv v

 


theorem fixedFactorQuotientLinearMap_injective
    (G : A) (hG : G ≠ 0) (V : Submodule F A)
    (hdiv : ∀ v : V, G ∣ (v : A)) :
    Function.Injective (fixedFactorQuotientLinearMap G hG V hdiv) := by
  intro v w h
  apply Subtype.ext
  rw [← mul_fixedFactorQuotientLinearMap G hG V hdiv v,
    ← mul_fixedFactorQuotientLinearMap G hG V hdiv w, h]

 
theorem fixedFactorQuotientLinearMap_ne_zero
    (G : A) (hG : G ≠ 0) (V : Submodule F A)
    (hdiv : ∀ v : V, G ∣ (v : A)) {v : V} (hv : v ≠ 0) :
    fixedFactorQuotientLinearMap G hG V hdiv v ≠ 0 := by
  intro hz
  apply hv
  apply (fixedFactorQuotientLinearMap_injective G hG V hdiv)
  simpa only [map_zero] using hz

 

 

def mappedFixedFactorQuotient (G : A) {V : Type*}
    [AddCommGroup V] [Module F V] (f : V →ₗ[F] A)
    (hdiv : ∀ v : V, G ∣ f v) (v : V) : A :=
  Classical.choose (hdiv v)

 
theorem mul_mappedFixedFactorQuotient (G : A) {V : Type*}
    [AddCommGroup V] [Module F V] (f : V →ₗ[F] A)
    (hdiv : ∀ v : V, G ∣ f v) (v : V) :
    G * mappedFixedFactorQuotient G f hdiv v = f v := by
  simpa only [mappedFixedFactorQuotient] using
    (Classical.choose_spec (hdiv v)).symm

 

def mappedFixedFactorQuotientLinearMap (G : A) (hG : G ≠ 0)
    {V : Type*} [AddCommGroup V] [Module F V] (f : V →ₗ[F] A)
    (hdiv : ∀ v : V, G ∣ f v) : V →ₗ[F] A where
  toFun := mappedFixedFactorQuotient G f hdiv
  map_add' v w := by
    apply mul_left_cancel₀ hG
    rw [mul_mappedFixedFactorQuotient, mul_add,
      mul_mappedFixedFactorQuotient, mul_mappedFixedFactorQuotient, map_add]
  map_smul' c v := by
    apply mul_left_cancel₀ hG
    rw [mul_mappedFixedFactorQuotient, mul_smul_comm,
      mul_mappedFixedFactorQuotient, map_smul]
    rfl

@[simp] theorem mappedFixedFactorQuotientLinearMap_apply
    (G : A) (hG : G ≠ 0) {V : Type*}
    [AddCommGroup V] [Module F V] (f : V →ₗ[F] A)
    (hdiv : ∀ v : V, G ∣ f v) (v : V) :
    mappedFixedFactorQuotientLinearMap G hG f hdiv v =
      mappedFixedFactorQuotient G f hdiv v := rfl

 
theorem mul_mappedFixedFactorQuotientLinearMap
    (G : A) (hG : G ≠ 0) {V : Type*}
    [AddCommGroup V] [Module F V] (f : V →ₗ[F] A)
    (hdiv : ∀ v : V, G ∣ f v) (v : V) :
    G * mappedFixedFactorQuotientLinearMap G hG f hdiv v = f v :=
  mul_mappedFixedFactorQuotient G f hdiv v

 
theorem mappedFixedFactorQuotientLinearMap_injective
    (G : A) (hG : G ≠ 0) {V : Type*}
    [AddCommGroup V] [Module F V] (f : V →ₗ[F] A)
    (hdiv : ∀ v : V, G ∣ f v) (hf : Function.Injective f) :
    Function.Injective (mappedFixedFactorQuotientLinearMap G hG f hdiv) := by
  intro v w h
  apply hf
  rw [← mul_mappedFixedFactorQuotientLinearMap G hG f hdiv v,
    ← mul_mappedFixedFactorQuotientLinearMap G hG f hdiv w, h]

 
theorem mappedFixedFactorQuotientLinearMap_ne_zero
    (G : A) (hG : G ≠ 0) {V : Type*}
    [AddCommGroup V] [Module F V] (f : V →ₗ[F] A)
    (hdiv : ∀ v : V, G ∣ f v) (hf : Function.Injective f)
    {v : V} (hv : v ≠ 0) :
    mappedFixedFactorQuotientLinearMap G hG f hdiv v ≠ 0 := by
  intro hz
  apply hv
  apply (mappedFixedFactorQuotientLinearMap_injective G hG f hdiv hf)
  simpa only [map_zero] using hz

end

end ProximityPrize.SubmissionLower.ContactFixedFactorQuotientLinear6750Research

#print axioms ProximityPrize.SubmissionLower.ContactFixedFactorQuotientLinear6750Research.mul_fixedFactorQuotientLinearMap
#print axioms ProximityPrize.SubmissionLower.ContactFixedFactorQuotientLinear6750Research.fixedFactorQuotientLinearMap_injective
#print axioms ProximityPrize.SubmissionLower.ContactFixedFactorQuotientLinear6750Research.fixedFactorQuotientLinearMap_ne_zero
#print axioms ProximityPrize.SubmissionLower.ContactFixedFactorQuotientLinear6750Research.mul_mappedFixedFactorQuotientLinearMap
#print axioms ProximityPrize.SubmissionLower.ContactFixedFactorQuotientLinear6750Research.mappedFixedFactorQuotientLinearMap_injective
