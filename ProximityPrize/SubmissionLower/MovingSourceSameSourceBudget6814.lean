import ProximityPrize.SubmissionLower.MovingSourceCoupledClearing6814
namespace ProximityPrize.SubmissionLower.MovingSourceSameSourceBudget6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
open MvPolynomial RCN095 WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingSourceCoupledClearing6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814

variable {K : Type} [Field K]
local notation "Poly5" => MvPolynomial (Fin 5) K

theorem pair_degrees_le (P J D : Poly5) (hP : P≠0) (hJ : J≠0) (hD : D≠0)
    (hcop : IsRelPrime J D) (hJP : J∣P) (hDP : D∣P) :
    (∀ w : Fin 5 → ℕ, weightedTotalDegree w J+weightedTotalDegree w D≤weightedTotalDegree w P) ∧
      order J+order D≤order P := by
  obtain ⟨R,hR⟩ := hcop.mul_dvd hJP hDP
  have hRne : R≠0 := by intro hz; apply hP; rw [hR,hz,mul_zero]
  constructor
  · intro w
    rw [hR,weight_mul _ _ _ (mul_ne_zero hJ hD) hRne,weight_mul _ _ _ hJ hD]
    omega
  · change J.degreeOf 1+D.degreeOf 1≤P.degreeOf 1
    rw [hR,degreeOf_mul_eq (mul_ne_zero hJ hD) hRne,degreeOf_mul_eq hJ hD]
    omega

end
end ProximityPrize.SubmissionLower.MovingSourceSameSourceBudget6814
