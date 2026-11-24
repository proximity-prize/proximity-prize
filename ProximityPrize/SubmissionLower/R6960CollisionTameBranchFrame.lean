import ProximityPrize.SubmissionLower.R6960CollisionTameBranch
import ProximityPrize.SubmissionLower.R6960CollisionTameDiscriminantLocalization
import ProximityPrize.SubmissionLower.R6960CollisionTameFrames

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Ideal IsLocalRing Module Polynomial Matrix NormalizedFiber
open scoped Polynomial Matrix BigOperators
open Lower6960.CollisionTame (gram_map integralsIncl)
open Lower6960.CollisionTame (integralClosure_torsionFree)

variable {k E : Type} [Field k] [Field E] [Algebra (Plane k) E]
  [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
  [FiniteDimensional (FractionRing (Plane k)) E] [Algebra.IsSeparable (FractionRing (Plane k)) E]

/-- At a branch where the frame denominator is invertible, the frame's
actual integral trace Gram matrix has order equal to its generic residue
corank. The proof localizes the lifted synthesis, without a global basis. -/
theorem branch_frame_trace_order {n : ℕ}
    (P : Ideal (Plane k)) [P.IsPrime] (q : Plane k) (pir : Irreducible q)
    (span : P=Ideal.span {q}) (p : ℕ) [CharP k p] (small : finrank (FractionRing (Plane k)) E<p)
    (u : Fin n→Order k E) (f : (Fin n→Plane k)→ₗ[Plane k]Order k E)
    (sum : ∀ t,f t=∑ i,t i • u i) (inj : Function.Injective f)
    (g : Plane k) (outside : g∉P) (clear : ∀ x : Order k E,∃ t,f t=g • x) :
    let T := tupleGram (integralTraceForm (A:=Plane k) (E:=E) (FractionRing (Plane k))) u
    emultiplicity q T.det=((n-((T.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank : ℕ):ℕ∞) := by
  classical
  let A := Plane k
  let F := FractionRing A
  let D := Localization.AtPrime P
  let : IsDiscreteValuationRing D := principal_prime_dvr P q pir.ne_zero span
  let : Algebra D F := (branchFractionHom (F:=F) P).toAlgebra
  let : IsFractionRing D F := branchFraction_isFractionRing (F:=F) P
  let : IsScalarTower A D F := IsScalarTower.of_algebraMap_eq (R:=A) (S:=D) (A:=F) fun r=>
    (branchFractionHom_apply (F:=F) P r).symm
  let : Algebra D E := ((algebraMap F E).comp (branchFractionHom (F:=F) P)).toAlgebra
  let : IsScalarTower D F E := IsScalarTower.of_algebraMap_eq (R:=D) (S:=F) (A:=E) fun _=>rfl
  let : IsScalarTower A D E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=D) (A:=E) fun r=>by
    change algebraMap A E r=algebraMap F E (branchFractionHom P (algebraMap A D r))
    rw [branchFractionHom_apply,IsScalarTower.algebraMap_apply A F E]
  let C := integralClosure D E
  let : CommRing C := @Subalgebra.toCommRing D E _ _ (inferInstance : Algebra D E) C
  let B := Order k E
  let incl : B→+*C := Lower6960.CollisionTame.integralsIncl
  let : Algebra B C := incl.toAlgebra
  let : Algebra A C := C.algebra'
  let : IsScalarTower A D C := IsScalarTower.of_algebraMap_eq (R:=A) (S:=D) (A:=C) fun r=>by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply A D E r
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (R:=A) (S:=B) (A:=C) fun a=>by
    apply Subtype.ext
    change algebraMap A E a=(incl (algebraMap A B a):E)
    rfl
  let : IsScalarTower B C E := IsScalarTower.of_algebraMap_eq (R:=B) (S:=C) (A:=E) fun _=>rfl
  let M := P.primeCompl
  let : IsLocalization (Algebra.algebraMapSubmonoid E M) E := by
    apply IsLocalization.of_le_isUnit
    rintro _ ⟨a,ha,rfl⟩
    have nz : a≠0 := fun eq=>(Ideal.mem_primeCompl_iff.mp ha) (eq.symm ▸ P.zero_mem)
    have ainj : Function.Injective (algebraMap A E) := by
      rw [IsScalarTower.algebraMap_eq A F E]
      exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ ainj).mpr nz)
  let : IsLocalization (Algebra.algebraMapSubmonoid B M) C :=
    IsLocalization.integralClosure (S:=E) (Rf:=D) (Sf:=E) M
  let j := (IsScalarTower.toAlgHom A B C).toLinearMap
  let : IsLocalizedModule M j := inferInstanceAs (IsLocalizedModule M (IsScalarTower.toAlgHom A B C).toLinearMap)
  have jinj : Function.Injective j := fun x y eq=>Subtype.ext (congrArg (fun t : C=>(t:E)) eq)
  obtain ⟨b,basis⟩ := localized_fibre_frame (A:=A) (R:=D) (M:=B) (P:=C) M j jinj f inj
    ⟨g,Ideal.mem_primeCompl_iff.mpr outside⟩ clear
  have repr (i : Fin n) : b i=incl (u i) := by
    rw [basis]
    have l : f (Pi.single i 1)=u i := by
      rw [sum,Finset.sum_eq_single i]
      · simp
      · intro j _ ji
        simp [Ne.symm ji]
        exact zero_smul A (u j)
      · simp
    rw [l]
    rfl
  let : Module.Free D C := Module.Free.of_basis b
  let : Module.Finite D C := Module.Finite.of_basis b
  let : Module.IsTorsionFree D C := Lower6960.CollisionTame.integralClosure_torsionFree (A:=D) (E:=E) F
  let : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension F
  let tr := integralTraceForm (A:=A) (E:=E) F
  let T := tupleGram tr u
  have localMatrix : T.map (algebraMap A D)=Algebra.traceMatrix D b := by
    calc
      _ = tupleGram (integralTraceForm (A:=D) (E:=E) F) (fun i=>incl (u i)) :=
        Lower6960.CollisionTame.gram_map (A:=A) (R:=D) (F:=F) (E:=E) u
      _ = _ := by
        rw [show (fun i=>incl (u i))=(b:Fin n→C) from funext fun i=>(repr i).symm]
        apply Matrix.ext
        intro i j
        change Algebra.intTrace D C (b i*b j)=Algebra.trace D C (b i*b j)
        rw [Algebra.intTrace_eq_trace]
  let charMap : k→+*ResidueField D := (residue D).comp ((algebraMap A D).comp (Polynomial.C.comp Polynomial.C))
  let : CharP (ResidueField D) p := charP_of_injective_ringHom charMap.injective p
  have h := trace_order_from_local_matrix P q pir span p small b T localMatrix
  simpa only [Fintype.card_fin] using h

#print axioms branch_frame_trace_order
end
end Lower6960.CollisionTame
