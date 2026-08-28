import ProximityPrize.SubmissionLower.BCHKSErrorLocatorKeyEquation6400

/-!
# Cancellation between two complementary locator factorizations

If one polynomial is simultaneously expressed through the complements of an
error set and a fixed defect set, multiplying by the missing nodal factors
and cancelling the nonzero agreement locator gives the exact full-error key
equation.  This is the set-theoretic algebra used by the common quotient.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial
open BCHKSErrorLocatorKeyEquation6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Convert a factorization by the two complement locators into an equation
between the corresponding nodal locators. -/
theorem nodal_keyEquation_of_complement_factorization
    {F I : Type} [Field F] [Fintype I] [DecidableEq I]
    (alpha : I ↪ F) (E Fixed : Finset I) (K S : F[X])
    (hfactor :
      selectedErrorLocator alpha Fixed * K =
        selectedErrorLocator alpha E * S) :
    Lagrange.nodal E (fun i ↦ alpha i) * K =
      Lagrange.nodal Fixed (fun i ↦ alpha i) * S := by
  classical
  have hselectedE : selectedErrorLocator alpha E ≠ 0 := by
    rw [selectedErrorLocator]
    exact Lagrange.nodal_ne_zero
  have hpartitionE := selectedErrorLocator_mul_agreementLocator alpha E
  have hpartitionFixed :=
    selectedErrorLocator_mul_agreementLocator alpha Fixed
  apply mul_left_cancel₀ hselectedE
  calc
    selectedErrorLocator alpha E *
          (Lagrange.nodal E (fun i ↦ alpha i) * K) =
        (selectedErrorLocator alpha E *
          Lagrange.nodal E (fun i ↦ alpha i)) * K := by
            rw [mul_assoc]
    _ = fullDomainLocator alpha * K := by rw [hpartitionE]
    _ = (selectedErrorLocator alpha Fixed *
          Lagrange.nodal Fixed (fun i ↦ alpha i)) * K := by
            rw [hpartitionFixed]
    _ = Lagrange.nodal Fixed (fun i ↦ alpha i) *
          (selectedErrorLocator alpha Fixed * K) := by
            ac_rfl
    _ = Lagrange.nodal Fixed (fun i ↦ alpha i) *
          (selectedErrorLocator alpha E * S) := by rw [hfactor]
    _ = selectedErrorLocator alpha E *
          (Lagrange.nodal Fixed (fun i ↦ alpha i) * S) := by
            ac_rfl

/-- Degree subtraction for a nonzero common quotient, stated in the strict
form used by the score-64 arithmetic. -/
theorem quotient_natDegree_lt_add_of_factor
    {F : Type} [Field F] (D K G : F[X]) (n h d : Nat)
    (hD : D ≠ 0) (hK : K ≠ 0)
    (hDdegree : D.natDegree = n - h)
    (hGdegree : G.natDegree < n + d)
    (hfactor : D * K = G) :
    K.natDegree < h + d := by
  have hdegree := congrArg Polynomial.natDegree hfactor
  rw [Polynomial.natDegree_mul hD hK, hDdegree] at hdegree
  omega

/-- Subtract an owner equation from an inhomogeneous received equation after
factoring the received-minus-owner word by its agreement locator. -/
theorem inhomogeneous_residual_eq_agreement_mul_semilinear
    {F : Type} [Field F] (sigma : F ≃+* F)
    (L A B C W P D : F[X])
    (hLmap : L.map sigma.toRingHom = L)
    (hfactor : L * D = W - P)
    (howner : C = A * P + B * P.map sigma.toRingHom) :
    A * W + B * W.map sigma.toRingHom - C =
      L * (A * D + B * D.map sigma.toRingHom) := by
  have hfrobenius := congrArg
    (Polynomial.map sigma.toRingHom) hfactor
  simp only [Polynomial.map_mul, Polynomial.map_sub, hLmap] at hfrobenius
  rw [howner]
  calc
    A * W + B * W.map sigma.toRingHom -
          (A * P + B * P.map sigma.toRingHom) =
        A * (W - P) +
          B * (W.map sigma.toRingHom - P.map sigma.toRingHom) := by ring
    _ = A * (L * D) + B * (L * D.map sigma.toRingHom) := by
      rw [← hfactor, ← hfrobenius]
    _ = L * (A * D + B * D.map sigma.toRingHom) := by ring

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
