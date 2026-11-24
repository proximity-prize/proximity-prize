import ProximityPrize.SubmissionLower.Y
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.DG
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace czE
noncomputable section
open scoped TensorProduct
variable {k E σ:Type} [Field k] [Field E] [Algebra k E]
theorem quotientBaseChange_tmul (I:Ideal (MvPolynomial σ k)) (c:E) (p:MvPolynomial σ k) :
    aPw I (c ⊗ₜ[k] Ideal.Quotient.mk I p) =
      c•Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap k E)))
        (MvPolynomial.map (algebraMap k E) p) := by
  unfold aPw
  rw [AlgEquiv.trans_apply,Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  change Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap k E)))
    (MvPolynomial.algebraTensorAlgEquiv k E (c ⊗ₜ[k] p))= _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
  exact (Ideal.Quotient.mkₐ E _).toLinearMap.map_smul c _
end
end czE
