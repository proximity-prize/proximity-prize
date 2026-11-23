import ProximityPrize.SubmissionLower.ZbpKj1d
set_option Elab.async false
set_option autoImplicit true
set_option maxHeartbeats 1000000
set_option maxRecDepth 1500
set_option backward.isDefEq.respectTransparency false
namespace bzK
noncomputable section
open Polynomial aR dN rW as9
section PolynomialFlow
variable {R:Type*} [CommRing R]
end PolynomialFlow
private def bgS {R:Type*} [CommRing R]
    (k :ao →+* R) (Q:af 4) (U:R[X]) :R[X] :=
  MvPolynomial.eval₂ (mapRingHom k) (fun i=>hasseDeriv i.val U) Q
private theorem rowTrajectory_degree {R:Type*} [CommRing R]
    (k :ao →+* R) (Q:af 4) (U:R[X]) {B:ℕ}
    (hQ:tB Q B) (hU:U.natDegree≤133671) :
    (bgS k Q U).natDegree≤B:= by
  classical
  unfold bgS
  rw [MvPolynomial.eval₂_eq]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  refine (natDegree_mul_le_of_le (Polynomial.natDegree_map_le) ?_).trans (hQ m hm)
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  change _≤(133671 - i.val)*m i
  rw [Nat.mul_comm]
  exact natDegree_pow_le_of_le _ ((natDegree_hasseDeriv_le _ _).trans (Nat.sub_le_sub_right hU _))
end
end bzK
