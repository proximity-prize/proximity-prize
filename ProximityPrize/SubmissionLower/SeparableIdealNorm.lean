import ProximityPrize.Benchmark.TargetLower

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Ideal_Norm_RelNorm

/-!
# Ideal norms over an explicitly separable, possibly imperfect base

Model label: gpt-5.

The pinned maximal-prime norm wrapper assumes that the base fraction field
is perfect. That hypothesis does not apply to K(T) in positive
characteristic. Here the normal closure is actually constructed from the
finite separable extension Frac(S)/Frac(R). Its embedding images, and hence
their compositum, are separable even though the ambient algebraic closure
of Frac(S) need not be separable over Frac(R).

The resulting prime and principal-ideal norm identities apply to arbitrary
elements of one fixed separable extension. They do not assume that an
individual test function defines a separable field extension. They do not
identify finite and infinite charts of a curve or prove a common-pole or
mixed-component-degree bound.
-/

namespace ProximityPrize.SubmissionLower.SeparableIdealNorm

noncomputable section

section Fields

variable (F E Ω : Type*) [Field F] [Field E] [Field Ω]
variable [Algebra F E] [Algebra F Ω] [Algebra.IsSeparable F E]

/-- Separability of the actual compositum of embedding images. No
separability hypothesis is imposed on the ambient field Ω/F. -/
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

/- These are the actual structures used in Ring.NormalClosure. The
underlying type and all maps remain the pinned integral-closure objects. -/
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

local instance : FaithfulSMul S E :=
  (faithfulSMul_iff_algebraMap_injective S E).mpr <|
    (FaithfulSMul.algebraMap_injective L E).comp
      (FaithfulSMul.algebraMap_injective S L)

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

/-- The fraction field of the constructed normal-closure ring is Galois
over Frac(R), using separability of Frac(S)/Frac(R), not perfectness. -/
theorem normalClosure_fractionRing_isGalois :
    IsGalois K (FractionRing T) := by
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext
  simpa using! IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv R K).symm (FractionRing.algEquiv T E).symm _

variable [IsDedekindDomain S]

/-- Finiteness is proved for the actual integral closure in the finite
separable normal closure; it is not supplied as a geometric assumption. -/
theorem normalClosure_finite : Module.Finite S T :=
  IsIntegralClosure.finite S L E T

local instance : Module.Finite S T := normalClosure_finite R S

local instance : Module.Finite R T := Module.Finite.trans S T

/-- The actual normal-closure ring is Dedekind under the stated hypotheses. -/
theorem normalClosure_isDedekindDomain : IsDedekindDomain T :=
  integralClosure.isDedekindDomain S L E

local instance : IsDedekindDomain T := normalClosure_isDedekindDomain R S

local instance : IsGalois K (FractionRing T) :=
  normalClosure_fractionRing_isGalois R S

variable [IsDedekindDomain R]

attribute [local instance] FractionRing.liftAlgebra

/-- The relative norm of an actual maximal prime is the contraction to
the power of its actual residue-field degree, over any explicitly
separable fraction-field extension. -/
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

/-- Full factorization of the norm of any nonzero ideal. Repeated prime
factors on the right retain their true ideal multiplicities. -/
theorem relNorm_eq_prod_prime_powers
    (I : Ideal S) (hI : I ≠ ⊥) :
    Ideal.relNorm R I =
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P : Ideal S ↦ (P.under R) ^ P.inertiaDeg R)).prod := by
  classical
  calc
    Ideal.relNorm R I =
        Ideal.relNorm R (UniqueFactorizationMonoid.normalizedFactors I).prod := by
      rw [Ideal.prod_normalizedFactors_eq_self hI]
    _ = ((UniqueFactorizationMonoid.normalizedFactors I).map
        (Ideal.relNorm R)).prod := map_multiset_prod (Ideal.relNorm R) _
    _ = _ := by
      congr 1
      apply Multiset.map_congr rfl
      intro P hP
      have hPzero : P ≠ ⊥ :=
        UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hP
      have hPprime : P.IsPrime := (Ideal.mem_normalizedFactors_iff hI).mp hP |>.1
      letI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hPzero hPprime
      exact relNorm_prime_eq_pow R S P (P.under R)

/-- Principal norm factorization for an arbitrary nonzero integral element
of the fixed extension. No separability condition is imposed on that
element viewed as a new function-field parameter. -/
theorem span_intNorm_eq_prod_prime_powers
    (x : S) (hx : x ≠ 0) :
    Ideal.span {Algebra.intNorm R S x} =
      ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {x})).map
        (fun P : Ideal S ↦ (P.under R) ^ P.inertiaDeg R)).prod := by
  rw [← Ideal.relNorm_singleton]
  exact relNorm_eq_prod_prime_powers R S (Ideal.span {x})
    (by simpa using hx)

/-- The scalar appearing in the preceding actual principal-ideal identity
is the field norm, after the canonical embedding in Frac(R). -/
theorem intNorm_maps_to_fieldNorm (x : S) :
    algebraMap R (FractionRing R) (Algebra.intNorm R S x) =
      Algebra.norm (FractionRing R)
        (algebraMap S (FractionRing S) x) :=
  Algebra.algebraMap_intNorm_fractionRing x

end Domains

end

end ProximityPrize.SubmissionLower.SeparableIdealNorm
