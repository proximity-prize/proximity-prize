import ProximityPrize.SubmissionLower.MovingSourceWeightedPairPoints6814
import ProximityPrize.SubmissionLower.MovingSourceMovingDegrees6814
namespace ProximityPrize.SubmissionLower.MovingSourceFactorIsolation6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
open MvPolynomial RCN084 RCN207

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K

theorem quotient_nonzero_at_regular_point (F G : Poly) (hdiv : G∣F)
    (x : Fin 3 → K) (hG : MvPolynomial.eval x G=0)
    (hreg : MvPolynomial.eval x (MvPolynomial.pderiv (1 : Fin 3) F)≠0) :
    ∃ Q : Poly, F=G*Q ∧ MvPolynomial.eval x Q≠0 := by
  obtain ⟨Q,hQ⟩ := hdiv
  refine ⟨Q,hQ,?_⟩
  rw [hQ,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,hG,zero_mul,add_zero] at hreg
  exact (mul_ne_zero_iff.mp hreg).2

theorem isolated_whole_of_factor (F G N A : Poly) (hdiv : G∣F)
    (x : Fin 3 → K) (hG : MvPolynomial.eval x G=0)
    (hreg : MvPolynomial.eval x (MvPolynomial.pderiv (1 : Fin 3) F)≠0)
    (hisolated : IsolatedPoint G N A x) : IsolatedPoint F N A x := by
  obtain ⟨Q,hQ,hQne⟩ := quotient_nonzero_at_regular_point F G hdiv x hG hreg
  intro P hprime hnotpoint hpoint hFmem hNmem
  have hQnot : Q∉P := by
    intro hmem
    apply hQne
    exact hpoint hmem
  have hGmem : G∈P := by
    rw [hQ] at hFmem
    exact (hprime.mem_or_mem hFmem).resolve_right hQnot
  exact hisolated P hprime hnotpoint hpoint hGmem hNmem

end
end ProximityPrize.SubmissionLower.MovingSourceFactorIsolation6814
