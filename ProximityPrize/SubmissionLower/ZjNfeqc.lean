import ProximityPrize.SubmissionLower.ZaQt7ib
import ProximityPrize.SubmissionLower.DB
set_option Elab.async false
namespace aZF
noncomputable section
open Polynomial
open cu (aZ)
open vq (apZ)

open ak0 (aTH adg)




private theorem coeffDx_mul (U V:aZ) :
    aTH (U*V)=U*aTH V+V*aTH U:= by
  classical
  rw [mul_comm V (aTH U)]
  apply MvPolynomial.ext
  intro m
  simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,MvPolynomial.coeff_mul,
    adg,map_sum,apZ,Finset.sum_add_distrib]
end
end aZF
