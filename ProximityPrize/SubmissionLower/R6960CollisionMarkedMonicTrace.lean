import ProximityPrize.SubmissionLower.R6960RetainedCrossingBasis
import ProximityPrize.SubmissionLower.R6960TraceSpecialization
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.AdjoinRoot

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial Algebra Module Matrix
open scoped Polynomial Matrix BigOperators

section Trace
variable {A R U V ι : Type*} [CommRing A] [CommRing R] [CommRing U] [CommRing V]
  [Algebra A U] [Algebra R V] [Fintype ι] [DecidableEq ι]

/-- Compatibility with the whole basis and scalar map transports the
multiplication matrices and the trace pairing. -/
theorem trace_matrix_map_of_basis (j : A→+*R) (a : Basis ι A U) (b : Basis ι R V) (φ : U→+*V)
    (scalar : ∀ c,φ (algebraMap A U c)=algebraMap R V (j c))
    (basis : ∀ i,φ (a i)=b i) : (traceMatrix A a).map j=traceMatrix R b := by
  have coords (x : U) (i : ι) : b.repr (φ x) i=j (a.repr x i) := by
    have expand : φ x=∑ l,j (a.repr x l) • b l := by
      rw [←a.sum_repr x,map_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [Algebra.smul_def,map_mul,scalar,basis,←Algebra.smul_def]
      simp only [a.repr_sum_self]
    rw [expand,b.repr_sum_self]
  have trace_map (x : U) : j (Algebra.trace A U x)=Algebra.trace R V (φ x) := by
    rw [trace_eq_matrix_trace a,trace_eq_matrix_trace b]
    unfold Matrix.trace
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply,Matrix.diag_apply,leftMulMatrix_eq_repr_mul,leftMulMatrix_eq_repr_mul,
      ←basis,←map_mul,coords]
  apply Matrix.ext
  intro i l
  simp only [Matrix.map_apply,traceMatrix_apply,traceForm_apply,←basis,←map_mul,trace_map]
end Trace

section Monic
variable {A R V : Type*} [CommRing A] [CommRing R] [CommRing V] [Algebra R V]

/-- The discriminant polynomial comes from the actual monic power-basis
order over the base, before specializing any coefficient. -/
def monicDisc {p : A[X]} (hp : p.Monic) : A := (traceMatrix A (AdjoinRoot.powerBasis' hp).basis).det

theorem monic_basis_trace {p : A[X]} (hp : p.Monic) (j : A→+*R)
    (γ : V) (root : aeval γ (p.map j)=0)
    (b : Basis (Fin p.natDegree) R V) (pow : ∀ i,b i=γ^(i:ℕ)) :
    (traceMatrix A (AdjoinRoot.powerBasis' hp).basis).map j=traceMatrix R b := by
  let ev := (algebraMap R V).comp j
  have rr : p.eval₂ ev γ=0 := by
    rw [aeval_def,eval₂_map] at root
    exact root
  let φ := AdjoinRoot.lift ev γ rr
  have scalar (c : A) : φ (algebraMap A (AdjoinRoot p) c)=algebraMap R V (j c) := by
    change AdjoinRoot.lift ev γ rr (AdjoinRoot.of p c)=_
    exact AdjoinRoot.lift_of rr
  have powers (i : Fin p.natDegree) : φ ((AdjoinRoot.powerBasis' hp).basis i)=b i := by
    rw [(AdjoinRoot.powerBasis' hp).basis_eq_pow,pow,map_pow]
    congr 1
    exact AdjoinRoot.lift_root rr
  exact trace_matrix_map_of_basis j (AdjoinRoot.powerBasis' hp).basis b φ scalar powers

theorem monic_disc_of_basis {p : A[X]} (hp : p.Monic) (j : A→+*R)
    (γ : V) (root : aeval γ (p.map j)=0)
    (b : Basis (Fin p.natDegree) R V) (pow : ∀ i,b i=γ^(i:ℕ)) :
    j (monicDisc hp)=Algebra.discr R b := by
  unfold monicDisc
  rw [Algebra.discr_def]
  exact (RingHom.map_det j _).trans (congrArg Matrix.det (monic_basis_trace hp j γ root b pow))
end Monic

section Coordinates
variable {A F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra A E] [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]

/-- The discriminant of the monic order clears all coordinates of every
actual normalized element, in the original power basis. -/
theorem monic_coordinates {p : A[X]} (hp : p.Monic) (γ : E) (root : aeval γ p=0)
    (b : Basis (Fin p.natDegree) F E) (pow : ∀ i,b i=γ^(i:ℕ))
    (x : integralClosure A E) :
    ∀ i,∃ c : A,algebraMap A F c=algebraMap A F (monicDisc hp)*b.repr (x:E) i := by
  classical
  let j := algebraMap A F
  have baseRoot : aeval γ (p.map j)=0 := by rw [aeval_map_algebraMap]; exact root
  let T : Matrix (Fin p.natDegree) (Fin p.natDegree) A := traceMatrix A (AdjoinRoot.powerBasis' hp).basis
  have eqT : T.map j=traceMatrix F b := monic_basis_trace hp j γ baseRoot b pow
  have integral : IsIntegral A γ := ⟨p,hp,root⟩
  have ib (i : Fin p.natDegree) : IsIntegral A (b i) := pow i ▸ integral.pow _
  choose t ht using fun i : Fin p.natDegree=>IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_trace (L:=F) (x.property.mul (ib i)))
  have exp : (T.map j)*ᵥb.equivFun (x:E)=fun i=>j (t i) := by
    rw [eqT,Algebra.traceMatrix_of_basis_mulVec]
    exact funext fun i=>(ht i).symm
  let v := T.adjugate *ᵥ t
  intro i
  refine ⟨v i,?_⟩
  have all : (fun i=>j (v i))=j T.det • b.equivFun (x:E) := by
    change (fun i=>j ((T.adjugate*ᵥt) i))=_
    have mv : (fun i=>j ((T.adjugate*ᵥt) i))=T.adjugate.map j *ᵥ (fun i=>j (t i)) :=
      funext fun i=>RingHom.map_mulVec j _ _ i
    have adj : T.adjugate.map j=(T.map j).adjugate := j.map_adjugate T
    rw [mv,adj,←exp,Matrix.mulVec_mulVec,
      Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec,RingHom.map_det]
    rfl
  exact congrFun all i

/-- At a place where the power-basis discriminant is a unit, the monic
order equals the actual integral closure in the root field. -/
theorem monic_order_eq_normalization {p : A[X]} (hp : p.Monic) (γ : E) (root : aeval γ p=0)
    (b : Basis (Fin p.natDegree) F E) (pow : ∀ i,b i=γ^(i:ℕ))
    (unit : IsUnit (monicDisc hp)) : Algebra.adjoin A {γ}=integralClosure A E := by
  let B := Algebra.adjoin A ({γ}:Set E)
  have gi : IsIntegral A γ := ⟨p,hp,root⟩
  apply le_antisymm
  · exact Algebra.adjoin_le (fun y hy=>(Set.mem_singleton_iff.mp hy).symm ▸ gi)
  · intro x hx
    choose c hc using monic_coordinates hp γ root b pow (⟨x,hx⟩:integralClosure A E)
    obtain ⟨d,hd⟩ := unit
    have dx : algebraMap A F (monicDisc hp) • x=∑ i,algebraMap A F (c i) • b i := by
      rw [←b.sum_repr x,Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul,←hc i]
    have isin : monicDisc hp • x∈B := by
      rw [←IsScalarTower.algebraMap_smul F,dx]
      apply B.sum_mem
      intro i _
      rw [IsScalarTower.algebraMap_smul F,pow]
      exact B.smul_mem (B.pow_mem (Algebra.subset_adjoin (Set.mem_singleton γ)) _) _
    have cancel : (↑d⁻¹:A) • (monicDisc hp • x)=x := by
      rw [smul_smul,←hd,Units.inv_mul,one_smul]
    exact cancel ▸ B.smul_mem isin _
end Coordinates

#print axioms monic_disc_of_basis
#print axioms monic_coordinates
#print axioms monic_order_eq_normalization
end
end Lower6960.CollisionMarked
