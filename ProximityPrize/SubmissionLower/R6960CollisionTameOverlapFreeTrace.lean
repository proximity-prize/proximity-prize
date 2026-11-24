import ProximityPrize.SubmissionLower.R6960CollisionTameOverlapUnit
import ProximityPrize.SubmissionLower.R6960LineEulerFree

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Polynomial Matrix Module LineEuler LaurentPolynomial
open scoped Polynomial Matrix BigOperators

variable {k U V M ι : Type*} [Field k] [CommRing U] [CommRing V] [CommRing M]
  [Algebra (Polynomial k) U] [Algebra (Polynomial k) V] [Algebra (Laurent k) M] [Fintype ι] [DecidableEq ι]

/-- The trace of the selected finite-free algebra specializes on its
actual common Laurent chart, including for a proper suborder. -/
theorem free_trace_matrix_on_torus (s : Bool) (b : Basis ι (Polynomial k) U)
    (f : ChartMap (k:=k) s U M) (loc : IsChartLocalization s f)
    (r : U→+*M) (agree : ∀ x,f x=r x) :
    (Algebra.traceMatrix (Polynomial k) b).map (chartEmbedding s (k:=k))=
      Algebra.traceMatrix (Laurent k) (localFreeBasis s b f loc) := by
  let B := localFreeBasis s b f loc
  have tr (x : U) : chartEmbedding s (Algebra.trace (Polynomial k) U x)=Algebra.trace (Laurent k) M (r x) := by
    rw [Algebra.trace_eq_matrix_trace b,Algebra.trace_eq_matrix_trace B]
    unfold Matrix.trace
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change chartEmbedding s ((Algebra.leftMulMatrix b x) i i)=((Algebra.leftMulMatrix B (r x)) i i)
    rw [Algebra.leftMulMatrix_eq_repr_mul,Algebra.leftMulMatrix_eq_repr_mul,
      show B i=r (b i) from (localFreeBasis_apply s b f loc i).trans (agree _),←map_mul,←agree]
    exact (localFreeBasis_repr s b f loc _ i).symm
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply,Algebra.traceMatrix_apply,Algebra.traceForm_apply,localFreeBasis_apply,
    agree,←map_mul]
  exact tr (b i*b j)

section Both
variable (bf : Basis ι (Polynomial k) U) (bi : Basis ι (Polynomial k) V)
  (ff : ChartMap (k:=k) false U M) (fi : ChartMap (k:=k) true V M)
  (lf : IsChartLocalization false ff) (li : IsChartLocalization true fi)

private theorem free_expansion (i : ι) :
    (∑ j,freeTransition bf bi ff fi lf li j i • localFreeBasis false bf ff lf j)=localFreeBasis true bi fi li i := by
  let fin := localFreeBasis false bf ff lf
  let inf := localFreeBasis true bi fi li
  have coord : freeTransition bf bi ff fi lf li *ᵥ Pi.single i (1:Laurent k) = fin.equivFun (inf i) := by
    rw [freeTransition_mulVec]
    have same : inf.equivFun (inf i)=Pi.single i 1 := by
      funext j
      rw [Basis.equivFun_apply,Basis.repr_self]
      simp only [Finsupp.single_eq_pi_single]
    rw [←same,LinearEquiv.symm_apply_apply]
  have repr : ∀ j,freeTransition bf bi ff fi lf li j i=fin.equivFun (inf i) j := by
    rw [Matrix.mulVec_single_one] at coord
    exact fun j=>congrFun coord j
  rw [show (∑ j,freeTransition bf bi ff fi lf li j i • fin j)=(∑ j,fin.equivFun (inf i) j • fin j)
    from Finset.sum_congr rfl (fun j _=>congrArg (· • fin j) (repr j))]
  exact (fin.equivFun_symm_apply (fin.equivFun (inf i))).symm.trans (fin.equivFun.symm_apply_apply (inf i))

/-- The actual trace determinants satisfy the squared transition law for
both normalized lines and reduced free suborders. -/
theorem free_trace_transition (r0 : U→+*M) (r1 : V→+*M)
    (h0 : ∀ x,ff x=r0 x) (h1 : ∀ x,fi x=r1 x) :
    invert ((Algebra.traceMatrix (Polynomial k) bi).det.toLaurent)=
      (freeTransition bf bi ff fi lf li).det^2*(Algebra.traceMatrix (Polynomial k) bf).det.toLaurent := by
  let G := freeTransition bf bi ff fi lf li
  let tr := Algebra.traceForm (Laurent k) M
  let X := Algebra.traceMatrix (Polynomial k) bf
  let Y := Algebra.traceMatrix (Polynomial k) bi
  let D := Algebra.traceMatrix (Laurent k) (localFreeBasis false bf ff lf)
  let N := Algebra.traceMatrix (Laurent k) (localFreeBasis true bi fi li)
  have change : N=G.transpose*D*G := by
    change tupleGram tr (localFreeBasis true bi fi li)=G.transpose*tupleGram tr (localFreeBasis false bf ff lf)*G
    rw [←tupleGram_change]
    exact congrArg (tupleGram tr) (funext fun i=>(free_expansion bf bi ff fi lf li i).symm)
  have detF : D.det=X.det.toLaurent := by
    have eq := congrArg Matrix.det (free_trace_matrix_on_torus false bf ff lf r0 h0)
    have det : (X.map (chartEmbedding false (k:=k))).det=chartEmbedding false X.det :=
      ((chartEmbedding false (k:=k)).toRingHom.map_det X).symm
    exact eq.symm.trans det
  have detI : N.det=invert Y.det.toLaurent := by
    have eq := congrArg Matrix.det (free_trace_matrix_on_torus true bi fi li r1 h1)
    have det : (Y.map (chartEmbedding true (k:=k))).det=chartEmbedding true Y.det :=
      ((chartEmbedding true (k:=k)).toRingHom.map_det Y).symm
    exact eq.symm.trans det
  change invert Y.det.toLaurent=G.det^2*X.det.toLaurent
  rw [←detI,change,det_mul,det_mul,det_transpose,detF]
  ring
end Both

#print axioms free_trace_transition
end
end Lower6960.CollisionTame
