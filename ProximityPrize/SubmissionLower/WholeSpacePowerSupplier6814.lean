import ProximityPrize.SubmissionLower.WholeSpacePowerCover6814
import ProximityPrize.SubmissionLower.WholeSpaceSourceKernel6814
namespace ProximityPrize.SubmissionLower.WholeSpacePowerSupplier6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open WholeSpacePowerBox6814 WholeSpacePowerCover6814 WholeSpaceSourceKernel6814
open WholeSpaceSourceCounts6814 SecondJetGlobalSupport

variable {K N I : Type*} [Field K] [Fintype N] [Fintype I]

theorem cofactor_of_not_power (J P : Poly (K := K)) (hJ : Irreducible J) (q : ℕ)
    (hnot : ¬J^q∣P) :
    ∃ e<q, ∃ Q : Poly (K := K), P=J^e*Q ∧ Q≠0 ∧ IsRelPrime J Q := by
  have hP : P≠0 := by intro hz; exact hnot (by rw [hz]; exact dvd_zero _)
  obtain ⟨e,Q,hnd,hEq⟩ := WfDvdMonoid.max_power_factor hP hJ
  have hQ : Q≠0 := by intro hz; apply hP; rw [hEq,hz,mul_zero]
  have he : e<q := by
    by_contra h
    exact hnot ((pow_dvd_pow J (by omega : q≤e)).trans ⟨Q,hEq⟩)
  exact ⟨e,he,Q,hEq,hQ,hJ.isRelPrime_iff_not_dvd.mpr hnd⟩

end
end ProximityPrize.SubmissionLower.WholeSpacePowerSupplier6814
