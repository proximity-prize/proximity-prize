import ProximityPrize.SubmissionLower.MovingSourceMixedOwnerRouting6814
import ProximityPrize.SubmissionLower.MovingSourceSameSourceBudget6814
namespace ProximityPrize.SubmissionLower.RetainedSharedRemainder6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open MvPolynomial RCN137 WholeSpaceCube6814 WholeSpaceCubeUniform6814
open UniqueCurvatureOwner6814 MovingSourceCoupledClearing6814
variable {K E : Type} [Field K] [Field E]

theorem third_root_divisor
    (psi : Poly (K:=K) →+* Polynomial E) (z : E)
    (P J D : Poly (K:=K)) (hne : psi P≠0)
    (hcop : IsRelPrime J D) (hJP : J∣P) (hDP : D∣P)
    (hJroot : (psi J).rootMultiplicity z=1)
    (hDroot : (psi D).rootMultiplicity z=1)
    (hpower : (Polynomial.X-Polynomial.C z)^3∣psi P) :
    ∃ Q : Poly (K:=K), Irreducible Q ∧ (psi Q).eval z=0 ∧ J*D*Q∣P := by
  obtain ⟨R,hEq⟩ := hcop.mul_dvd hJP hDP
  have hRm : psi R≠0 := by
    intro hz
    apply hne
    rw [hEq,map_mul,hz,mul_zero]
  have hJDm : psi J*psi D≠0 := by
    intro hz
    apply hne
    rw [hEq,map_mul,map_mul,hz,zero_mul]
  have horder := (Polynomial.le_rootMultiplicity_iff hne).mpr hpower
  rw [hEq,map_mul,map_mul,Polynomial.rootMultiplicity_mul (mul_ne_zero hJDm hRm),
    Polynomial.rootMultiplicity_mul hJDm,hJroot,hDroot] at horder
  have hRroot : (psi R).eval z=0 := (Polynomial.rootMultiplicity_pos hRm).mp (by omega)
  have hR : R≠0 := by intro hz; exact hRm (by rw [hz,map_zero])
  let ev : Poly (K:=K) →+* E := (Polynomial.evalRingHom z).comp psi
  obtain ⟨Q,hQ,hQroot⟩ := exists_normalizedFactorSet_zero ev R hR hRroot
  have hspec := normalizedFactorSet_spec R Q hQ
  refine ⟨Q,hspec.1,hQroot,?_⟩
  rw [hEq]
  exact mul_dvd_mul_left (J*D) hspec.2

end
end ProximityPrize.SubmissionLower.RetainedSharedRemainder6815
