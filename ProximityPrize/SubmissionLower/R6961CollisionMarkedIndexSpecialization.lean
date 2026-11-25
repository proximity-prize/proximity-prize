import ProximityPrize.SubmissionLower.R6961MarkedTranslatedEquation
import ProximityPrize.SubmissionLower.R6960QuadraticProjection
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Module
import ProximityPrize.SubmissionLower.R6960CollisionTameDiscriminant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ProximityPrize.SubmissionLower.R6960CollisionMarkedIndexSpecialization
import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option Elab.async false

-- merged module R6961CollisionMarkedFibreNormalization
section Merged_R6961CollisionMarkedFibreNormalization

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
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
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedFibreNormalization

-- merged module R6961CollisionMarkedFibreIndex
section Merged_R6961CollisionMarkedFibreIndex

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
noncomputable section
open Algebra Module Matrix Polynomial Lower6960.CollisionTame
open scoped Matrix Polynomial BigOperators

variable {A K B V : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing B] [Algebra A B] [CommRing V] [IsReduced V] [Algebra A V]
  [Algebra K V] [IsScalarTower A K V] [FiniteDimensional K V]

/-- A genuine finite free order in the reduced generic fibre has a
comparison determinant against its normalization. The determinant clears
every integral element, including the word idempotent, back into the
original order. -/
theorem reduced_fibre_index {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℕ) [CharP K p] (small : finrank K V<p)
    (φ : B→ₐ[A]V) (b : Basis I A B)
    (bk : Basis I K V) (induced : ∀ i,bk i=φ (b i)) :
    ∃ (n : Basis I A (integralClosure A V)) (D : Matrix I I A),
      D.det≠0 ∧ (traceMatrix A n).det≠0 ∧
      (∃ lift : B→ₐ[A]integralClosure A V,
        (∀ x,(lift x:V)=φ x) ∧ D=n.toMatrix (fun i=>lift (b i))) ∧
      traceMatrix A b=D.transpose*traceMatrix A n*D ∧
      (∀ v : V,IsIntegral A v→∃ u : B,φ u=algebraMap A V D.det*v) := by
  classical
  let N := integralClosure A V
  let : Module.Finite A B := Module.Finite.of_basis b
  let lift : B→ₐ[A]N := φ.codRestrict N (fun x=>(Algebra.IsIntegral.isIntegral x).map φ)
  obtain ⟨n0,nk0,h0⟩ := reduced_normalization_basis (A:=A) p small
  let t : Fin (finrank K V) ≃ I := (Fintype.equivFinOfCardEq (finrank_eq_card_basis bk).symm).symm
  let n := n0.reindex t
  let nk := nk0.reindex t
  have hn (i : I) : nk i=(n i:V) := by
    rw [show nk i=nk0 (t.symm i) from Basis.reindex_apply _ _ _,
      show n i=n0 (t.symm i) from Basis.reindex_apply _ _ _]
    exact h0 _
  let D : Matrix I I A := fun i j=>n.repr (lift (b j)) i
  let j := algebraMap A K
  have expand (i : I) : (∑ l,j (D l i) • nk l)=bk i := by
    calc
      _ = (↑(∑ l,D l i • n l : N):V) := by
        rw [show ((∑ l,D l i • n l : N):V)=∑ l,((D l i • n l : N):V) from map_sum N.val _ _]
        apply Finset.sum_congr rfl
        intro l _
        rw [hn,Subalgebra.coe_smul,IsScalarTower.algebraMap_smul]
      _ = (lift (b i):V) := congrArg Subtype.val (n.sum_repr (lift (b i)))
      _ = _ := (induced i).symm
  have ae : D.map j=nk.toMatrix bk := by
    apply Matrix.ext
    intro i l
    change j (D i l)=nk.repr (bk l) i
    rw [←expand l,nk.repr_sum_self]
  have an : (D.map j).det≠0 := by
    have h : (bk.toMatrix nk)*(D.map j)=1 := by rw [ae,Basis.toMatrix_mul_toMatrix_flip]
    exact Matrix.det_ne_zero_of_left_inverse h
  have dn : D.det≠0 := fun zero=>an (((RingHom.map_det j D).symm).trans (zero ▸ map_zero j))
  have map_b : (traceMatrix A b).map j=traceMatrix K bk :=
    trace_matrix_map_of_basis j b bk φ.toRingHom (fun a=>(φ.commutes a).trans (IsScalarTower.algebraMap_apply A K V a))
      (fun i=>(induced i).symm)
  have map_n : (traceMatrix A n).map j=traceMatrix K nk :=
    trace_matrix_map_of_basis j n nk N.val.toRingHom (fun a=>IsScalarTower.algebraMap_apply A K V a)
      (fun i=>(hn i).symm)
  have identity : traceMatrix A b=D.transpose*traceMatrix A n*D := by
    apply Matrix.map_injective (f:=j) (IsFractionRing.injective A K)
    have joined : (D.transpose*traceMatrix A n*D).map j =
        D.transpose.map j * (traceMatrix A n).map j * D.map j := by
      change j.mapMatrix (D.transpose*traceMatrix A n*D)=
        j.mapMatrix D.transpose * j.mapMatrix (traceMatrix A n) * j.mapMatrix D
      rw [map_mul,map_mul]
    change (traceMatrix A b).map j=(D.transpose*traceMatrix A n*D).map j
    rw [map_b,joined]
    have trans : D.transpose.map j=(D.map j).transpose := rfl
    change tupleGram (traceForm K V) bk=D.transpose.map j * (traceMatrix A n).map j * D.map j
    rw [trans,map_n]
    change tupleGram (traceForm K V) bk=(D.map j).transpose*tupleGram (traceForm K V) nk*(D.map j)
    rw [←tupleGram_change]
    exact congrArg (tupleGram (traceForm K V)) (funext fun i=>(expand i).symm)
  have nn : (traceMatrix A n).det≠0 := by
    have nd : (traceForm K V).Nondegenerate := by
      apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
      apply bot_unique
      intro x hx
      change x=0
      exact IsReduced.eq_zero x ((Lower6960.TraceSpecialization.trace_radical p small x).mp hx)
    have mat : traceMatrix K nk=(traceForm K V).toMatrix nk := by
      apply Matrix.ext
      intro i l
      rw [traceMatrix_apply,LinearMap.BilinForm.toMatrix_apply]
    intro zero
    apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero nk).mp nd
    rw [←mat,←map_n]
    change (j.mapMatrix (traceMatrix A n)).det = 0
    rw [←RingHom.map_det]
    exact zero ▸ map_zero j
  refine ⟨n,D,dn,nn,⟨lift,fun _=>rfl,rfl⟩,identity,?_⟩
  intro v hv
  let x : N := ⟨v,hv⟩
  let c := D.adjugate *ᵥ n.equivFun x
  let u := b.equivFun.symm c
  have ueq : u=∑ i,c i • b i := b.equivFun_symm_apply c
  have mapped : n.equivFun (lift u)=D*ᵥc := by
    rw [ueq,map_sum,map_sum]
    funext i
    simp only [Finset.sum_apply,Basis.equivFun_apply,Matrix.mulVec,dotProduct,D]
    apply Finset.sum_congr rfl
    intro l _
    have csmul : lift (c l • b l) = c l • lift (b l) := lift.toLinearMap.map_smul _ _
    rw [csmul,n.repr.map_smul,Finsupp.smul_apply,smul_eq_mul,mul_comm]
  have by_det : D*ᵥc=D.det • n.equivFun x := by
    change D*ᵥ(D.adjugate*ᵥn.equivFun x)=_
    rw [Matrix.mulVec_mulVec,Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec]
  have lift_eq : lift u=D.det • x := by
    apply n.equivFun.injective
    rw [mapped,by_det,n.equivFun.map_smul]
  refine ⟨u,?_⟩
  have h := congrArg Subtype.val lift_eq
  rw [Subalgebra.coe_smul] at h
  change φ u = (D.det:A) • v at h
  simpa only [Algebra.smul_def] using h

omit [IsPrincipalIdealRing A] [IsReduced V] in
/-- The marked projector is always integral over the base, independently
of whether it belongs to the original order. -/
theorem idempotent_integral (v : V) (idem : v^2=v) : IsIntegral A v := by
  refine ⟨Polynomial.X^2-Polynomial.X,monic_X_pow_sub (by rw [degree_X]; norm_num),?_⟩
  simp [idem]

#print axioms reduced_fibre_index
end
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedFibreIndex

-- merged module R6961CollisionMarkedIndexSpecialization
section Merged_R6961CollisionMarkedIndexSpecialization

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6961.CollisionMarked
noncomputable section
open Algebra TensorProduct Module Matrix Polynomial
open scoped Matrix Polynomial TensorProduct

variable {R B N I : Type*} {k : Type} [CommRing R] [Field k]
  [CommRing B] [CommRing N] [Algebra R B] [Algebra R N]
  [Fintype I] [DecidableEq I]

/-- Reduction of a genuine comparison map, its coordinate matrix, and
both true trace matrices along one base field map. -/
theorem comparison_tensor_specialization (j:R→+*k)
    (b:Basis I R B) (n:Basis I R N) (φ:B→ₐ[R]N) :
    let : Algebra R k := j.toAlgebra
    let a := b.baseChange k
    let c := n.baseChange k
    let ψ := Algebra.TensorProduct.map (AlgHom.id k k) φ
    (n.toMatrix (fun i=>φ (b i))).map j=LinearMap.toMatrix a c ψ.toLinearMap ∧
    (traceMatrix R n).map j=traceMatrix k c ∧
    (traceMatrix R b).map j=traceMatrix k a := by
  let : Algebra R k := j.toAlgebra
  refine ⟨?_,?_,?_⟩
  · apply Matrix.ext
    intro i l
    rw [Matrix.map_apply,Basis.toMatrix_apply,LinearMap.toMatrix_apply]
    change j (n.repr (φ (b l)) i) = (n.baseChange k).repr
      ((Algebra.TensorProduct.map (AlgHom.id k k) φ) (b.baseChange k l)) i
    rw [b.baseChange_apply k,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,n.baseChange_repr_tmul k,
      Algebra.smul_def,mul_one]
    rfl
  · exact trace_matrix_map_of_basis j n (n.baseChange k)
      (Algebra.TensorProduct.includeRight (R:=R) (A:=k) (B:=N)).toRingHom
      (fun _=>Algebra.TensorProduct.includeRight.commutes _) (fun i=>(n.baseChange_apply k i).symm)
  · exact trace_matrix_map_of_basis j b (b.baseChange k)
      (Algebra.TensorProduct.includeRight (R:=R) (A:=k) (B:=B)).toRingHom
      (fun _=>Algebra.TensorProduct.includeRight.commutes _) (fun i=>(b.baseChange_apply k i).symm)

variable {B0 N0 : Type} [CommRing B0] [CommRing N0] [Algebra (Polynomial k) B0] [Algebra (Polynomial k) N0]

/-- A comparison determinant of the actual original fibre cannot vanish
at a transverse branch point of the actual lifted trace matrix. -/
theorem comparison_transverse_unit {J : Type} [Fintype J] [DecidableEq J]
    (b : Basis J (Polynomial k) B0) (n : Basis J (Polynomial k) N0) (φ : B0→ₐ[(Polynomial k)]N0)
    (D : Matrix J J (Polynomial k)) (coords : D=n.toMatrix (fun i=>φ (b i)))
    (dn : D.det≠0) (nn : (traceMatrix (Polynomial k) n).det≠0)
    (trace : traceMatrix (Polynomial k) b=D.transpose*traceMatrix (Polynomial k) n*D)
    (p : ℕ) [CharP k p] (small : Fintype.card J<p)
    (x : k) {A F : Type} [CommRing A] [Field F]
    (along : Matrix J J A) (spec : A→+*k) (gen : A→+*F) (inj : Function.Injective gen)
    (point : along.map spec=(traceMatrix (Polynomial k) b).map (evalRingHom x))
    (transverse : (traceMatrix (Polynomial k) b).det.rootMultiplicity x≤Fintype.card J-(along.map gen).rank) :
    D.det.eval x≠0 := by
  classical
  let j := evalRingHom x
  let : Algebra (Polynomial k) k := j.toAlgebra
  obtain ⟨dc,nc,bc⟩ := comparison_tensor_specialization j b n φ
  rw [←coords] at dc
  have raw : j.mapMatrix (D.transpose*traceMatrix (Polynomial k) n*D)=traceMatrix k (b.baseChange k) :=
    trace ▸ bc
  exact Lower6960.TraceIndex.transverse_unit (b.baseChange k) (n.baseChange k) p small
    (Algebra.TensorProduct.map (AlgHom.id k k) φ) x D (traceMatrix (Polynomial k) n) dn nn dc nc raw
    along spec gen inj (trace ▸ point) (trace ▸ transverse)

#print axioms comparison_transverse_unit
end
end Lower6961.CollisionMarked

end Merged_R6961CollisionMarkedIndexSpecialization
