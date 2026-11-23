import ProximityPrize.SubmissionLower.R6960CollisionMarkedFibreIndex
import ProximityPrize.SubmissionLower.R6960TraceIndex
import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
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

variable {B0 N0 : Type} [CommRing B0] [CommRing N0] [Algebra k[X] B0] [Algebra k[X] N0]

/-- A comparison determinant of the actual original fibre cannot vanish
at a transverse branch point of the actual lifted trace matrix. -/
theorem comparison_transverse_unit {J : Type} [Fintype J] [DecidableEq J]
    (b : Basis J k[X] B0) (n : Basis J k[X] N0) (φ : B0→ₐ[k[X]]N0)
    (D : Matrix J J k[X]) (coords : D=n.toMatrix (fun i=>φ (b i)))
    (dn : D.det≠0) (nn : (traceMatrix k[X] n).det≠0)
    (trace : traceMatrix k[X] b=D.transpose*traceMatrix k[X] n*D)
    (p : ℕ) [CharP k p] (small : Fintype.card J<p)
    (x : k) {A F : Type} [CommRing A] [Field F]
    (along : Matrix J J A) (spec : A→+*k) (gen : A→+*F) (inj : Function.Injective gen)
    (point : along.map spec=(traceMatrix k[X] b).map (evalRingHom x))
    (transverse : (traceMatrix k[X] b).det.rootMultiplicity x≤Fintype.card J-(along.map gen).rank) :
    D.det.eval x≠0 := by
  classical
  let j := evalRingHom x
  let : Algebra k[X] k := j.toAlgebra
  obtain ⟨dc,nc,bc⟩ := comparison_tensor_specialization j b n φ
  rw [←coords] at dc
  have raw : j.mapMatrix (D.transpose*traceMatrix k[X] n*D)=traceMatrix k (b.baseChange k) :=
    trace ▸ bc
  exact TraceIndex.transverse_unit (b.baseChange k) (n.baseChange k) p small
    (Algebra.TensorProduct.map (AlgHom.id k k) φ) x D (traceMatrix k[X] n) dn nn dc nc raw
    along spec gen inj (trace ▸ point) (trace ▸ transverse)

#print axioms comparison_transverse_unit
end
end Lower6960.CollisionMarked
