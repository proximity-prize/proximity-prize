import ProximityPrize.Benchmark.TargetLower

import Mathlib.RingTheory.Ideal.Norm.RelNorm

namespace ProximityPrize.SubmissionLower.SeparableIdealNorm

set_option linter.overlappingInstances false

noncomputable section

section Fields

variable (F E Ω : Type*) [Field F] [Field E] [Field Ω]
variable [Algebra F E] [Algebra F Ω] [Algebra.IsSeparable F E]

theorem normalClosure_isSeparable :
    Algebra.IsSeparable F (IntermediateField.normalClosure F E Ω) := by
  letI : ∀ σ : E →ₐ[F] Ω, Algebra.IsSeparable F σ.fieldRange :=
    fun σ ↦ AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField σ)
  change Algebra.IsSeparable F
    (⨆ σ : E →ₐ[F] Ω, σ.fieldRange : IntermediateField F Ω)
  infer_instance

end Fields

section Domains

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [Algebra R S] [Module.IsTorsionFree R S]

local instance : Algebra (FractionRing R) (FractionRing S) :=
  FractionRing.liftAlgebra _ _

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "E" => IntermediateField.normalClosure (FractionRing R)
  (FractionRing S) (AlgebraicClosure (FractionRing S))
local notation3 "T" => Ring.NormalClosure R S

local instance : Algebra S E :=
  ((algebraMap L E).comp (algebraMap S L)).toAlgebra

local instance : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl

local instance : Algebra T E :=
  inferInstanceAs (Algebra (integralClosure S E) E)

local instance : IsScalarTower S T E :=
  inferInstanceAs (IsScalarTower S (integralClosure S E) E)

local instance : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E

local instance : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E

local instance : IsScalarTower R S E := IsScalarTower.to₁₂₄ R S L E

local instance : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E

variable [Module.Finite R S]
variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

local instance : FiniteDimensional L E := Module.Finite.right K L E

local instance : IsFractionRing T E :=
  integralClosure.isFractionRing_of_finite_extension L E

local instance : Algebra.IsSeparable K E :=
  normalClosure_isSeparable K L (AlgebraicClosure L)

local instance : IsGalois K E where

local instance : Algebra.IsSeparable L E :=
  Algebra.isSeparable_tower_top_of_isSeparable K L E

theorem normalClosure_fractionRing_isGalois :
    IsGalois K (FractionRing T) := by
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext
  simpa using! IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv R K).symm (FractionRing.algEquiv T E).symm _

variable [IsDedekindDomain S]

omit [IsDomain S] in
local instance : Module.Finite S T :=
  IsIntegralClosure.finite S L E T

omit [IsDomain S] in
local instance : Module.Finite R T := Module.Finite.trans S T

omit [IsDomain S] in
local instance : IsDedekindDomain T :=
  integralClosure.isDedekindDomain S L E

omit [IsDomain S] in
local instance : IsGalois K (FractionRing T) :=
  normalClosure_fractionRing_isGalois R S

variable [IsDedekindDomain R]

attribute [local instance] FractionRing.liftAlgebra

theorem relNorm_prime_eq_pow
    (P : Ideal S) (p : Ideal R) [P.LiesOver p]
    [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ P.inertiaDeg R := by
  obtain ⟨Q, hQmax, hQP⟩ :
      ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h := Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  have : IsGalois (FractionRing S) (FractionRing T) :=
    IsGalois.tower_top_of_isGalois
      (FractionRing R) (FractionRing S) (FractionRing T)
  rwa [← Ideal.relNorm_relNorm R S,
    Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    Ideal.inertiaDeg_tower (R := R) P Q, pow_mul,
    pow_left_inj (Ideal.inertiaDeg_pos Q S).ne'] at h

end Domains

end

end ProximityPrize.SubmissionLower.SeparableIdealNorm
