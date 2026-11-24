import ProximityPrize.SubmissionLower.A1
import ProximityPrize.SubmissionLower.ZceTCvc
set_option Elab.async false
set_option autoImplicit true
namespace atb
noncomputable section
open Polynomial K1 aR dN wH lB Tx
open scoped BigOperators
private theorem cr1 {P:gQ} {H :Shape} (h:yy P H) :
    Supported H P:= by
  intro m hm
  refine ⟨?_,?_,?_⟩
  · exact (Finset.le_sup (f := fun a=>a.sum fun _ e=>e) hm).trans h.1
  · have hw:=(MvPolynomial.le_weightedTotalDegree Fin.val hm).trans h.2.1
    simpa only [Finsupp.weight_apply,smul_eq_mul,Nat.mul_comm] using hw
  · exact (MvPolynomial.le_degreeOf_of_mem_support _ hm).trans h.2.2
private abbrev constants :ao →+* cH :=qY.comp Polynomial.C
private abbrev center :cH :=qY Polynomial.X
private theorem ayL (P:ao[X]) : (P.map constants).eval center=qY P:= by
  rw [Polynomial.eval_map]
  change P.eval₂ (qY.comp Polynomial.C) (qY Polynomial.X)=qY P
  rw [← Polynomial.hom_eval₂,Polynomial.eval₂_C_X]
end
end atb
