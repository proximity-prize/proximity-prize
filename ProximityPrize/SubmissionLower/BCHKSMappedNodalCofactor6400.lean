import ProximityPrize.SubmissionLower.BCHKSReedSolomonCofactor6400

/-! # Nodal divisibility over a polynomial coefficient ring -/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- Pairwise-coprime field-valued nodal factors remain pairwise coprime after
embedding their coefficients in a polynomial ring. -/
theorem mapped_outsideAgreementLocator_dvd
    {F I : Type} [Field F] [Fintype I] [DecidableEq I]
    (alpha : I ↪ F) (S T : Finset I) (P : F[X][X])
    (hzero : ∀ i ∈ S, i ∉ T →
      P.eval (Polynomial.C (alpha i)) = 0) :
    (outsideAgreementLocator alpha S T).map
        (Polynomial.C : F →+* F[X]) ∣ P := by
  classical
  rw [outsideAgreementLocator, Lagrange.nodal, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    rw [← Polynomial.C_sub]
    exact IsUnit.map (Polynomial.C : F →+* F[X])
      (sub_ne_zero_of_ne (alpha.injective.ne hij)).isUnit
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
    exact hzero i (Finset.mem_sdiff.mp hi).1
      (Finset.mem_sdiff.mp hi).2

end ProximityPrize.SubmissionLower
