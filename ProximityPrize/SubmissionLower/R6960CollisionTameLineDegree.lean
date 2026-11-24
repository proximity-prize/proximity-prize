import ProximityPrize.SubmissionLower.R6960CollisionTameDiscriminant
import ProximityPrize.SubmissionLower.R6960LineEulerFree
import Mathlib.RingTheory.Trace.Basic
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 5200000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.CollisionTame
noncomputable section
open Polynomial Matrix LaurentPolynomial LineEuler Module
open scoped Polynomial Matrix BigOperators
variable {k E ι : Type*} [Field k] [Field E] [Algebra (Laurent k) E]
  [Fintype ι] [DecidableEq ι]
theorem trace_matrix_on_torus (s : Bool) (b : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) s)) :
    (Algebra.traceMatrix (Polynomial k) b).map (chartEmbedding s (k:=k))=
      Algebra.traceMatrix (Laurent k) (localBasis s b) := by
  have tr (x : chartOrder (k:=k) (E:=E) s) : chartEmbedding s (Algebra.trace (Polynomial k) _ x)=
      Algebra.trace (Laurent k) _ (chartOrderMap s x) := by
    rw [Algebra.trace_eq_matrix_trace b,Algebra.trace_eq_matrix_trace (localBasis s b)]
    unfold Matrix.trace
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change chartEmbedding s ((Algebra.leftMulMatrix b x) i i)=
      ((Algebra.leftMulMatrix (localBasis s b) (chartOrderMap s x)) i i)
    rw [Algebra.leftMulMatrix_eq_repr_mul,Algebra.leftMulMatrix_eq_repr_mul,
      localBasis_apply,←map_mul,localBasis_repr]
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply,Algebra.traceMatrix_apply,Algebra.traceForm_apply,localBasis_apply,←map_mul]
  exact tr (b i*b j)
private theorem transition_expansion
    (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true)) (i : ι) :
    (∑ j,normalizedTransition bf bi j i • localBasis false bf j)=localBasis true bi i := by
  let fin := localBasis false bf
  let inf := localBasis true bi
  have coord : normalizedTransition bf bi *ᵥ Pi.single i (1:Laurent k) = fin.equivFun (inf i) := by
    rw [normalizedTransition_mulVec]
    have s : inf.equivFun (inf i)=Pi.single i 1 := by
      funext j
      rw [Basis.equivFun_apply,Basis.repr_self]
      simp only [Finsupp.single_eq_pi_single]
    rw [←s,LinearEquiv.symm_apply_apply]
  have repr : ∀ j,normalizedTransition bf bi j i=fin.equivFun (inf i) j := by
    rw [Matrix.mulVec_single_one] at coord
    exact fun j=>congrFun coord j
  rw [show (∑ j,normalizedTransition bf bi j i • fin j)=(∑ j,fin.equivFun (inf i) j • fin j)
    from Finset.sum_congr rfl (fun j _=>congrArg (· • fin j) (repr j))]
  exact (fin.equivFun_symm_apply (fin.equivFun (inf i))).symm.trans (fin.equivFun.symm_apply_apply (inf i))
theorem normalized_trace_transition
    (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true)) :
    invert ((Algebra.traceMatrix (Polynomial k) bi).det.toLaurent)=
      (normalizedTransition bf bi).det^2*(Algebra.traceMatrix (Polynomial k) bf).det.toLaurent := by
  let G := normalizedTransition bf bi
  let X := Algebra.traceMatrix (Polynomial k) bf
  let Z := Algebra.traceMatrix (Polynomial k) bi
  let M := (Algebra.traceMatrix (Laurent k) (localBasis false bf))
  let N := (Algebra.traceMatrix (Laurent k) (localBasis true bi))
  have change : N=G.transpose*M*G := by
    let tr := Algebra.traceForm (Laurent k) (torusOrder (k:=k) (E:=E))
    change tupleGram tr (localBasis true bi)=G.transpose*tupleGram tr (localBasis false bf)*G
    rw [←tupleGram_change]
    exact congrArg (tupleGram tr) (funext fun i=>(transition_expansion bf bi i).symm)
  have finDet : M.det=X.det.toLaurent := by
    have h := congrArg Matrix.det (trace_matrix_on_torus false bf)
    have det : (X.map (chartEmbedding false (k:=k))).det=chartEmbedding false X.det :=
      ((chartEmbedding false (k:=k)).toRingHom.map_det X).symm
    exact h.symm.trans det
  have infDet : N.det=infinityEmbedding Z.det := by
    have h := congrArg Matrix.det (trace_matrix_on_torus true bi)
    have det : (Z.map (chartEmbedding true (k:=k))).det=chartEmbedding true Z.det :=
      ((chartEmbedding true (k:=k)).toRingHom.map_det Z).symm
    exact h.symm.trans det
  change infinityEmbedding Z.det=G.det^2*X.det.toLaurent
  rw [←infDet,change,det_mul,det_mul,det_transpose,finDet]
  ring
theorem normalized_line_discriminant_degree
    (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true))
    (nonzero : (Algebra.traceMatrix (Polynomial k) bf).det≠0) :
    ∃ d : ℤ,(normalizedTransition bf bi).det.degree=(d:WithBot ℤ) ∧
      ((Algebra.traceMatrix (Polynomial k) bf).det.natDegree:ℤ)≤-2*d := by
  let G := normalizedTransition bf bi
  let X := Algebra.traceMatrix (Polynomial k) bf
  let Z := Algebra.traceMatrix (Polynomial k) bi
  obtain ⟨c,d,cn,dc⟩ := unit_monomial G.det ((Matrix.isUnit_iff_isUnit_det G).mp (normalizedTransition_unit bf bi))
  have h := normalized_trace_transition bf bi
  change infinityEmbedding Z.det=G.det^2*X.det.toLaurent at h
  rw [dc] at h
  have product : infinityEmbedding Z.det=LaurentPolynomial.C (c^2)*(T (d+d)*X.det.toLaurent) := by
    rw [T_add,map_pow,h,pow_two]
    ring
  refine ⟨d,by rw [dc,degree_C_mul_T _ _ cn],?_⟩
  let n : ℤ := X.det.natDegree
  have alive : (X.det.toLaurent).coeff n≠0 := Finsupp.mem_support_iff.mp (by
    rw [support_coeff_toLaurent]
    exact Finset.mem_map.mpr ⟨_,natDegree_mem_support_of_nonzero nonzero,rfl⟩)
  have supported : infinityEmbedding Z.det∈AddMonoidAlgebra.supported k k (Set.Iic ((0:ℕ):ℤ)) := by
    rw [←range_shiftPolynomial 0]
    exact ⟨Z.det,by rw [shiftPolynomial_apply,Nat.cast_zero,T_zero,one_mul]⟩
  by_contra bad
  have neg : ¬ n+(d+d)∈Set.Iic ((0:ℕ):ℤ) := by
    change ¬n+(d+d)≤0
    change ¬n≤-2*d at bad
    omega
  have z := AddMonoidAlgebra.mem_supported'.mp supported _ neg
  rw [product,←single_eq_C,AddMonoidAlgebra.coeff_single_zero_mul,coeff_shift,add_sub_cancel_right] at z
  exact mul_ne_zero (pow_ne_zero 2 cn) alive z
#print axioms trace_matrix_on_torus
#print axioms normalized_trace_transition
#print axioms normalized_line_discriminant_degree
end
end Lower6960.CollisionTame
