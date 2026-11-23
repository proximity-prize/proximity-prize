import ProximityPrize.SubmissionLower.R6960CollisionMarkedMonicTrace
import ProximityPrize.SubmissionLower.R6960QuadraticProjection
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Module

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial Module Algebra
open scoped Polynomial

variable {A K V : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing V] [Algebra A V] [Algebra K V] [IsScalarTower A K V]
  [FiniteDimensional K V]

private theorem small_fields_separable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : ℕ) [CharP K p] (small : finrank K L<p) : Algebra.IsSeparable K L := by
  constructor
  intro x
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  exact (separable_iff_derivative_ne_zero (minpoly.irreducible hx)).mpr
    (CurvatureSquares.derivative_ne_zero_of_natDegree_pos_lt_char p _ (minpoly.natDegree_pos hx)
      ((minpoly.natDegree_le x).trans_lt small))

/-- The normalization of the already specialized reduced generic fibre
is finite over its polynomial base. Each field factor is normalized
separately, and the original order embeds into that finite module. -/
theorem reduced_normalization_finite [IsReduced V] (p : ℕ) [CharP K p]
    (small : finrank K V<p) : Module.Finite A (integralClosure A V) := by
  classical
  let : IsArtinianRing V := isArtinian_of_tower K (inferInstance : IsArtinian K V)
  let I := MaximalSpectrum V
  let L (i : I) := V ⧸ i.asIdeal
  let : ∀ i : I, Field (L i) := fun i=>@Ideal.Quotient.field V _ i.asIdeal i.isMaximal
  let : ∀ i : I, Algebra K (L i) := fun i=>inferInstanceAs (Algebra K (V ⧸ i.asIdeal))
  let : ∀ i : I, Algebra A (L i) := fun i=>inferInstanceAs (Algebra A (V ⧸ i.asIdeal))
  let : ∀ i : I, IsScalarTower A K (L i) := fun i=>
    IsScalarTower.of_algebraMap_eq (R:=A) (S:=K) (A:=L i) fun a=>by
      change Ideal.Quotient.mk _ (algebraMap A V a)=Ideal.Quotient.mk _ (algebraMap K V (algebraMap A K a))
      rw [←IsScalarTower.algebraMap_apply A K V]
  let projK (i : I) : V→ₗ[K]L i := (IsScalarTower.toAlgHom K V (L i)).toLinearMap
  have surj (i : I) : Function.Surjective (projK i) := Ideal.Quotient.mk_surjective
  let : ∀ i : I, FiniteDimensional K (L i) := fun i=>FiniteDimensional.of_surjective (projK i) (surj i)
  let : ∀ i : I, Algebra.IsSeparable K (L i) := fun i=>small_fields_separable p
    ((LinearMap.finrank_le_finrank_of_surjective (f:=projK i) (surj i)).trans_lt small)
  let : ∀ i : I, Module.Finite A (integralClosure A (L i)) := fun i=>
    IsIntegralClosure.finite A K (L i) (integralClosure A (L i))
  let proj (i : I) : V→ₐ[A]L i := IsScalarTower.toAlgHom A V (L i)
  let j : integralClosure A V →ₗ[A] (∀ i : I,integralClosure A (L i)) := {
    toFun := fun v i=>⟨proj i (v:V),v.property.map (proj i)⟩
    map_add' := fun x y=>funext fun i=>Subtype.ext (map_add (proj i) _ _)
    map_smul' := fun a x=>funext fun i=>Subtype.ext ((proj i).toLinearMap.map_smul a (x:V)) }
  have ji : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply (IsArtinianRing.equivPi V).injective
    funext i
    exact congrArg Subtype.val (congrFun h i)
  exact Module.Finite.of_injective j ji

omit [IsPrincipalIdealRing A] in
/-- Integral closure in a finite generic algebra localizes back to the
whole generic algebra. This applies to the normalization of a fibre
without identifying it with the fibre of the normalization. -/
theorem integral_elements_localize (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K V] [IsScalarTower A K V] [FiniteDimensional K V] :
    IsLocalizedModule (nonZeroDivisors A) (integralClosure A V).val.toLinearMap := by
  let j := (integralClosure A V).val.toLinearMap
  constructor
  · intro r
    rw [Module.End.isUnit_iff]
    change Function.Bijective (fun x : V=>(r:A) • x)
    have rK : algebraMap A K (r:A)≠0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (mem_nonZeroDivisors_iff_ne_zero.mp r.property)
    refine ⟨?_,?_⟩
    · intro x y eq
      apply smul_right_injective V rK
      simpa only [IsScalarTower.algebraMap_smul K] using eq
    · intro y
      refine ⟨(algebraMap A K (r:A))⁻¹ • y,?_⟩
      change (r:A) • ((algebraMap A K (r:A))⁻¹ • y)=y
      calc
        _ = (algebraMap A K (r:A)) • ((algebraMap A K (r:A))⁻¹ • y) :=
          (IsScalarTower.algebraMap_smul K _ _).symm
        _ = y := by rw [smul_smul,mul_inv_cancel₀ rK,one_smul]
  · intro x
    have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
    have : Algebra.IsAlgebraic A V := Algebra.IsAlgebraic.trans A K V
    obtain ⟨r,nz,h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R:=A) x).exists_integral_multiple
    exact ⟨⟨⟨r • x,h⟩,⟨r,mem_nonZeroDivisors_iff_ne_zero.mpr nz⟩⟩,rfl⟩
  · intro a b eq
    exact ⟨1,congrArg (1 • ·) (Subtype.ext eq)⟩

/-- Each reduced normalized fibre order has a basis of precisely the
generic rank, and this basis extends to a basis in the generic fibre. -/
theorem reduced_normalization_basis [IsReduced V] (p : ℕ) [CharP K p]
    (small : finrank K V<p) :
    ∃ (b : Basis (Fin (finrank K V)) A (integralClosure A V))
      (bk : Basis (Fin (finrank K V)) K V),∀ i,bk i=(b i:V) := by
  let N := integralClosure A V
  let : Module.Finite A N := reduced_normalization_finite (K:=K) p small
  let : Module.IsTorsionFree A V := Module.IsTorsionFree.of_smul_eq_zero fun r x hx=>by
    by_cases h : r=0
    · exact Or.inl h
    · have nz := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr h
      rw [←IsScalarTower.algebraMap_smul K] at hx
      exact Or.inr ((smul_eq_zero_iff_right nz).mp hx)
  let : Module.IsTorsionFree A N := inferInstanceAs (Module.IsTorsionFree A (integralClosure A V))
  let j := N.val.toLinearMap
  let : IsLocalizedModule (nonZeroDivisors A) j := integral_elements_localize K
  let b := Module.finBasis A N
  let bk := b.ofIsLocalizedModule K (nonZeroDivisors A) j
  have rank : finrank A N=finrank K V := by
    simpa only [Fintype.card_fin] using (finrank_eq_card_basis bk).symm
  refine ⟨b.reindex (finCongr rank),bk.reindex (finCongr rank),fun i=>?_⟩
  rw [Basis.reindex_apply,Basis.reindex_apply,Basis.ofIsLocalizedModule_apply]
  rfl

#print axioms reduced_normalization_finite
#print axioms reduced_normalization_basis
end
end Lower6960.CollisionMarked
