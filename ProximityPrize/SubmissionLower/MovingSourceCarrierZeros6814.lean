import ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
open MvPolynomial RCN136 RCN207 SecondJetCoefficients SecondJetClearedHelper
open SecondJetCarrierDichotomy MovingSourceClearing6814

variable {K E : Type*} [Field K] [Field E]

theorem helper_dvd_of_generic_root
    (P : WholeSpaceCube6814.Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (phi : MvPolynomial (Fin 4) K →+* E)
    (hker : ∀ A, phi A=0 ↔ F ∣ A)
    (s : ℕ) (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hH : phi (2*RCN313.polyH K F)≠0)
    (hroot : ((asS P).map phi).eval (ratio phi F)=0) : F ∣ helper P F s 0 := by
  apply (hker _).mp
  have hh := mapped_helper P F phi s 0 hS hH
  simpa only [Nat.sub_zero,Function.iterate_zero,id_eq,hroot,mul_zero] using hh

end
end ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814
