import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSecondContactConstraintMap6660Research

 







namespace ProximityPrize.SubmissionLower.ContactSecondContactKernel6660Research

open ProximityPrize.Benchmark
open ContactSecondContactSFreeInterpolation6660Research
open ContactSecondContactUVSpan6660Research
open ContactSecondContactConstraintMap6660Research
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.checkUnivs false

noncomputable section

variable (K : Type*) [Field K]

abbrev LowJet := ContactSecondContactUVSpan6660Research.LowJet K

 

def boundedTranslatedColumn (D w C rCap m : ℕ) (x u0 u1 : K)
    (c : CoefficientIndex D w C rCap) : uvSpan K m C rCap :=
  ⟨lowJet K m (secondContactTranslation K x u0 u1
      (MvPolynomial.monomial (columnExponent c) 1)),
    lowJet_translation_column_mem_uvSpan K m x u0 u1 c 1⟩

 
def localConstraint (D w C rCap m : ℕ) (x u0 u1 : K) :
    (CoefficientIndex D w C rCap → K) →ₗ[K] uvSpan K m C rCap where
  toFun θ := ∑ c : CoefficientIndex D w C rCap,
    θ c • boundedTranslatedColumn K D w C rCap m x u0 u1 c
  map_add' θ η := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a θ := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul,
      RingHom.id_apply]

theorem monomial_eq_smul_one {D w C rCap : ℕ}
    (c : CoefficientIndex D w C rCap) (a : K) :
    MvPolynomial.monomial (columnExponent c) a =
      a • MvPolynomial.monomial (columnExponent c) (1 : K) := by
  rw [MvPolynomial.smul_monomial]
  simp

 

theorem localConstraint_coe (D w C rCap m : ℕ) (x u0 u1 : K)
    (θ : CoefficientIndex D w C rCap → K) :
    ((localConstraint K D w C rCap m x u0 u1 θ : uvSpan K m C rCap) :
        LowJet K m) =
      lowJet K m (secondContactTranslation K x u0 u1
        (reconstruct K D w C rCap θ)) := by
  classical
  rw [show localConstraint K D w C rCap m x u0 u1 θ =
      ∑ c : CoefficientIndex D w C rCap,
        θ c • boundedTranslatedColumn K D w C rCap m x u0 u1 c by rfl]
  change (uvSpan K m C rCap).subtype
      (∑ c : CoefficientIndex D w C rCap,
        θ c • boundedTranslatedColumn K D w C rCap m x u0 u1 c) = _
  rw [map_sum]
  simp only [map_smul]
  change (∑ c : CoefficientIndex D w C rCap,
      θ c • lowJet K m (secondContactTranslation K x u0 u1
        (MvPolynomial.monomial (columnExponent c) 1))) = _
  rw [reconstruct, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [monomial_eq_smul_one K c (θ c), map_smul, map_smul]

abbrev GlobalTarget (I : Type*) (m C rCap : ℕ) :=
  I → uvSpan K m C rCap

theorem localTarget_finrank_le (m C rCap : ℕ) :
    Module.finrank K (uvSpan K m C rCap) ≤ localUVRankBound m C rCap :=
  span_range_finrank_le K m C rCap (uvSpanVector K m C rCap)

theorem globalTarget_finrank_le {I : Type*} [Fintype I]
    (m C rCap : ℕ) :
    Module.finrank K (GlobalTarget K I m C rCap) ≤
      Fintype.card I * localUVRankBound m C rCap := by
  letI : Module.Finite K (uvSpan K m C rCap) :=
    FiniteDimensional.span_of_finite K
      (Set.finite_range (uvSpanVector K m C rCap))
  change Module.finrank K (I → uvSpan K m C rCap) ≤ _
  rw [Module.finrank_pi_fintype]
  calc
    (∑ _i : I, Module.finrank K (uvSpan K m C rCap)) ≤
        ∑ _i : I, localUVRankBound m C rCap := by
      apply Finset.sum_le_sum
      intro i hi
      exact localTarget_finrank_le K m C rCap
    _ = Fintype.card I * localUVRankBound m C rCap := by simp

def globalConstraint {I : Type*} [Fintype I]
    (D w C rCap m : ℕ) (nodes u0 u1 : I → K) :
    (CoefficientIndex D w C rCap → K) →ₗ[K]
      GlobalTarget K I m C rCap :=
  LinearMap.pi fun i => localConstraint K D w C rCap m
    (nodes i) (u0 i) (u1 i)

 

theorem exists_nonzero_kernel_array {I : Type*} [Fintype I]
    (D w C rCap m : ℕ) (nodes u0 u1 : I → K)
    (hgate : Fintype.card I * localUVRankBound m C rCap <
      coefficientCount D w C rCap) :
    ∃ θ : CoefficientIndex D w C rCap → K,
      θ ≠ 0 ∧ globalConstraint K D w C rCap m nodes u0 u1 θ = 0 := by
  classical
  letI : Module.Finite K (uvSpan K m C rCap) :=
    FiniteDimensional.span_of_finite K
      (Set.finite_range (uvSpanVector K m C rCap))
  by_contra hnone
  have hinj : Function.Injective
      (globalConstraint K D w C rCap m nodes u0 u1) := by
    intro θ η heq
    by_contra hne
    apply hnone
    refine ⟨θ - η, sub_ne_zero.mpr hne, ?_⟩
    rw [map_sub, heq, sub_self]
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, coefficient_index_card] at hdim
  have hupper := globalTarget_finrank_le K (I := I) m C rCap
  exact (Nat.not_le_of_gt hgate) (hdim.trans hupper)

theorem equations_of_globalConstraint_zero {I : Type*} [Fintype I]
    (D w C rCap m : ℕ) (nodes u0 u1 : I → K)
    (θ : CoefficientIndex D w C rCap → K)
    (hzero : globalConstraint K D w C rCap m nodes u0 u1 θ = 0) :
    ∀ i : I, HasSecondContactEquations K (reconstruct K D w C rCap θ)
      (nodes i) (u0 i) (u1 i) m := by
  intro i
  have hi : localConstraint K D w C rCap m (nodes i) (u0 i) (u1 i) θ = 0 :=
    congrFun hzero i
  have hlow : lowJet K m (secondContactTranslation K (nodes i) (u0 i) (u1 i)
      (reconstruct K D w C rCap θ)) = 0 := by
    rw [← localConstraint_coe K D w C rCap m (nodes i) (u0 i) (u1 i) θ]
    exact congrArg Subtype.val hi
  intro j hj
  have hcoeff := congrFun hlow (⟨j, hj⟩ : Fin m)
  exact hcoeff

 


theorem exists_row6660_nonzero_secondContact_interpolant
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ globalCoefficientBox IRSProfile.Field 5848704 131071 717 9 ∧
      ∀ i : IRSProfile.Index,
        HasSecondContactEquations IRSProfile.Field Q
          (IRSProfile.domain i) (u0 i) (u1 i) 32 := by
  have hcard : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  have hgate : Fintype.card IRSProfile.Index * localUVRankBound 32 717 9 <
      coefficientCount 5848704 131071 717 9 := by
    rw [hcard]
    exact row6660_kernel_gate
  obtain ⟨θ, hθ, hzero⟩ := exists_nonzero_kernel_array IRSProfile.Field
    5848704 131071 717 9 32
    (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1 hgate
  refine ⟨reconstruct IRSProfile.Field 5848704 131071 717 9 θ,
    reconstruct_ne_zero IRSProfile.Field 5848704 131071 717 9 θ hθ,
    reconstruct_mem_globalCoefficientBox IRSProfile.Field 5848704 131071 717 9 θ,
    ?_⟩
  exact equations_of_globalConstraint_zero IRSProfile.Field
    5848704 131071 717 9 32
    (fun i : IRSProfile.Index => IRSProfile.domain i) u0 u1 θ hzero

 

theorem exists_row6660_nonzero_root_forcing_interpolant
    (u0 u1 : IRSProfile.Index → IRSProfile.Field)
    (h2 : (2 : IRSProfile.Field) ≠ 0) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ globalCoefficientBox IRSProfile.Field 5848704 131071 717 9 ∧
      ∀ (P : Polynomial IRSProfile.Field) (gamma : IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ 131071 →
        182772 ≤ support.card →
        (∀ i ∈ support,
          P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        specialization IRSProfile.Field P gamma Q = 0 := by
  obtain ⟨Q, hQ, hcaps, hequations⟩ :=
    exists_row6660_nonzero_secondContact_interpolant u0 u1
  refine ⟨Q, hQ, hcaps, ?_⟩
  intro P gamma support hP hcard hvalues
  exact row6660_specialization_eq_zero Q P gamma u0 u1 support h2 hcaps
    hequations hP hcard hvalues

end

end ProximityPrize.SubmissionLower.ContactSecondContactKernel6660Research

#print axioms ProximityPrize.SubmissionLower.ContactSecondContactKernel6660Research.localConstraint_coe
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactKernel6660Research.exists_nonzero_kernel_array
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactKernel6660Research.exists_row6660_nonzero_secondContact_interpolant
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactKernel6660Research.exists_row6660_nonzero_root_forcing_interpolant
