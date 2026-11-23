import ProximityPrize.SubmissionLower.R6960LineEulerComparison
import ProximityPrize.SubmissionLower.R6960LineEulerPolynomial
import ProximityPrize.SubmissionLower.R6960LineEulerTransition

set_option Elab.async false
set_option maxHeartbeats 4400000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.LineEuler
noncomputable section
open LaurentPolynomial Polynomial Module Submodule
open scoped Polynomial BigOperators

variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]

/-- Apply the transition to the polynomial lattice at infinity. -/
def transitionLattice (G : Matrix ι ι (Laurent k)) : Submodule k (ι→Laurent k) :=
  (upperLattice k ι 0).map ((Matrix.toLin' G).restrictScalars k)

/-- Global sections identify with the two chart lattices' intersection. -/
abbrev H0 (G : Matrix ι ι (Laurent k)) := ↥(finiteLattice k ι⊓transitionLattice G)

/-- First cohomology is the actual Laurent quotient by the two chart images. -/
abbrev H1 (G : Matrix ι ι (Laurent k)) := (ι→Laurent k) ⧸ (finiteLattice k ι⊔transitionLattice G)

private theorem action_commutes (G : Matrix ι ι (Laurent k)) (N : ℕ) (A : Matrix ι ι k[X])
    (clear : G=(T (R:=k) (N:ℤ)) • A.map (infinityEmbedding (k:=k))) (v : ι→k[X]) :
    Matrix.toLin' G (shiftVector 0 v)=shiftVector N (Matrix.toLin' A v) := by
  funext i
  rw [Matrix.toLin'_apply,shiftVector_apply,Matrix.toLin'_apply]
  change (∑ j, G i j * (T (0:ℤ)*infinityEmbedding (v j))) =
    T (N:ℤ)*infinityEmbedding (∑ j, A i j*v j)
  rw [clear,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.map_apply,T_zero,one_mul,map_mul,mul_assoc]

/-- The transition lattice is the image of the polynomial matrix inside
its shifted comparison lattice. -/
theorem transition_eq_cleared (G : Matrix ι ι (Laurent k)) (N : ℕ) (A : Matrix ι ι k[X])
    (clear : G=(T (R:=k) (N:ℤ)) • A.map (infinityEmbedding (k:=k))) :
    transitionLattice G=((Matrix.toLin' A).range.restrictScalars k).map (shiftVector N) := by
  rw [transitionLattice,←range_shiftVector 0]
  ext v
  constructor
  · rintro ⟨w,⟨p,rfl⟩,rfl⟩
    exact ⟨Matrix.toLin' A p,⟨p,rfl⟩,(action_commutes G N A clear p).symm⟩
  · rintro ⟨w,⟨p,rfl⟩,rfl⟩
    exact ⟨shiftVector 0 p,⟨p,rfl⟩,action_commutes G N A clear p⟩

private def relative_quotient (G : Matrix ι ι (Laurent k)) (N : ℕ) (A : Matrix ι ι k[X])
    (clear : G=(T (R:=k) (N:ℤ)) • A.map (infinityEmbedding (k:=k))) :
    ((ι→k[X]) ⧸ (Matrix.toLin' A).range) ≃ₗ[k]
      ((upperLattice k ι N) ⧸ (transitionLattice G).comap (upperLattice k ι N).subtype) := by
  let B := upperLattice k ι N
  let D := (transitionLattice G).comap B.subtype
  let R := (Matrix.toLin' A).range.restrictScalars k
  change ((ι→k[X]) ⧸ R) ≃ₗ[k] (B ⧸ D)
  let e : (ι→k[X]) ≃ₗ[k] B := upperEquiv N
  refine Submodule.Quotient.equiv R D e ?_
  ext v
  change (∃ p∈R,e p=v) ↔ (v:ι→Laurent k)∈transitionLattice G
  rw [transition_eq_cleared G N A clear]
  change (∃ p∈R,e p=v) ↔ ∃ p∈R,shiftVector N p=(v:ι→Laurent k)
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨p,hp,rfl⟩
  · rintro ⟨p,hp,eq⟩
    exact ⟨p,hp,Subtype.ext eq⟩

/-- The one-line Euler index of a Laurent transition. Both spaces are
finite-dimensional, and the sign convention is the one in which `t`
raises the index of a rank-one transition from `1` to `2`. -/
theorem euler_index (G : Matrix ι ι (Laurent k)) (unit : IsUnit G) :
    FiniteDimensional k (H0 G) ∧ FiniteDimensional k (H1 G) ∧
    ∃ d : ℤ,G.det.degree=(d:WithBot ℤ) ∧
      (finrank k (H0 G):ℤ)-(finrank k (H1 G):ℤ)=(Fintype.card ι:ℤ)+d := by
  obtain ⟨N,A,clear⟩ := clear_transition G
  obtain ⟨an,d,d_eq,d_value⟩ := transition_degree G unit N A clear
  obtain ⟨finiteQ,degQ⟩ := polynomial_cokernel A an
  obtain ⟨finiteI,degI⟩ := finite_inter_upper (k:=k) (ι:=ι) N
  let B := upperLattice k ι N
  let C := transitionLattice G
  let F := finiteLattice k ι
  let equiv := relative_quotient G N A clear
  let : FiniteDimensional k (B ⧸ C.comap B.subtype) :=
    FiniteDimensional.of_surjective equiv.toLinearMap equiv.surjective
  have inc : C≤B := by
    intro v hv
    change v∈transitionLattice G at hv
    rw [transition_eq_cleared G N A clear] at hv
    obtain ⟨p,_,rfl⟩ := hv
    exact (upperEquiv N p).property
  have relativeDim : finrank k (B ⧸ C.comap B.subtype)=A.det.natDegree := equiv.finrank_eq.symm.trans degQ
  obtain ⟨finite0,finite1,eq⟩ := compare_lattices F C B inc (finite_sup_upper N)
  refine ⟨finite0,finite1,d,d_eq,?_⟩
  rw [relativeDim,degI] at eq
  change finrank k (H0 G)+A.det.natDegree=finrank k (H1 G)+Fintype.card ι*(N+1) at eq
  rw [Nat.mul_add,Nat.mul_one] at eq
  have eqZ := congrArg (fun n : ℕ=>(n:ℤ)) eq
  push_cast at eqZ
  omega

#print axioms euler_index
end
end Lower6960.LineEuler
