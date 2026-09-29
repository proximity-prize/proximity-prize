import ProximityPrize.SubmissionLower.RelativeContactOrder

namespace ProximityPrize.SubmissionLower.RelativeContactOrder6814
open MvPolynomial ContactOrderBridge
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

/-- The actual contact filtration at a received affine value. -/
def contactSubmodule (x u0 u1 : K) (m : ℕ) : Submodule K (Poly4 K) :=
  (MvPolynomial.restrictSupport K {d | m ≤ Finsupp.weight localWeights d}).comap
    (localize K x u0 u1).toLinearMap

theorem mem_contactSubmodule (x u0 u1 : K) (m : ℕ) (Q : Poly4 K) :
    Q ∈ contactSubmodule K x u0 u1 m ↔ ContactAtLeast K x u0 u1 m Q := by
  rfl

def factorMultiplication (F : Poly4 K) : Poly4 K →ₗ[K] Poly4 K where
  toFun Q := F * Q
  map_add' Q R := mul_add F Q R
  map_smul' a Q := by simp [MvPolynomial.smul_eq_C_mul, mul_left_comm]

theorem factorMultiplication_ker (x u0 u1 : K) (m : ℕ) (F : Poly4 K) (hF : F ≠ 0) :
    LinearMap.ker ((contactSubmodule K x u0 u1 m).mkQ.comp
      (factorMultiplication K F)) =
        contactSubmodule K x u0 u1 (m - contactOrder K x u0 u1 F) := by
  ext Q
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  change ContactAtLeast K x u0 u1 m (F * Q) ↔
    ContactAtLeast K x u0 u1 (m - contactOrder K x u0 u1 F) Q
  exact contact_mul_iff K x u0 u1 m F Q hF

/-- Multiplication by F on the shifted contact-jet quotient. Its kernel
has been computed exactly above, not supplied as an adapter hypothesis. -/
def factorJetMap (x u0 u1 : K) (m : ℕ) (F : Poly4 K) (hF : F ≠ 0) :
    (Poly4 K ⧸ contactSubmodule K x u0 u1 (m - contactOrder K x u0 u1 F)) →ₗ[K]
      (Poly4 K ⧸ contactSubmodule K x u0 u1 m) :=
  (contactSubmodule K x u0 u1 (m - contactOrder K x u0 u1 F)).liftQ
    ((contactSubmodule K x u0 u1 m).mkQ.comp (factorMultiplication K F))
    (by rw [factorMultiplication_ker K x u0 u1 m F hF])

theorem factorJetMap_injective (x u0 u1 : K) (m : ℕ) (F : Poly4 K) (hF : F ≠ 0) :
    Function.Injective (factorJetMap K x u0 u1 m F hF) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  rw [factorMultiplication_ker K x u0 u1 m F hF]

end
end ProximityPrize.SubmissionLower.RelativeContactOrder6814

#print axioms ProximityPrize.SubmissionLower.RelativeContactOrder6814.factorJetMap_injective
