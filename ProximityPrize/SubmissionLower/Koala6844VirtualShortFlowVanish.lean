import ProximityPrize.SubmissionLower.Koala6844VirtualShortFirstJetContact
import ProximityPrize.SubmissionLower.Koala6844ReceiptsFlowClearing


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open ContactOrderBridge LocatorLowQuotient
open Koala6844Receipts (ClearedForm)

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000

variable {K I : Type*} [Field K]

theorem specialization_vanish_of_cleared_contact
    (P A N : MvPolynomial (Fin 4) K) (w q m a dA L U B : ℕ)
    (ha : 0 < a) (hm : 0 < m)
    (hbox : P ∈ nestedCoefficientBox K (m*a+q*dA) w L U B)
    (hclear : ClearedForm A N q P)
    (x : I ↪ K) (u0 u1 : I → K) (S : Finset I) (hS : a ≤ S.card)
    (hcontact : ∀ i ∈ S, ContactAtLeast K (x i) (u0 i) (u1 i) m P)
    (f Q : Polynomial K) (g : K) (hf : f.natDegree ≤ w)
    (hvalues : ∀ i ∈ S, f.eval (x i) = u0 i+g*u1 i)
    (hdeg : (RCN319.specialization K f g A).natDegree = dA)
    (havoid : ∀ i ∈ S, (RCN319.specialization K f g A).eval (x i) ≠ 0)
    (heq : RCN319.specialization K f g N = RCN319.specialization K f g A*Q) :
    RCN319.specialization K f g P = 0 := by
  classical
  let φ := (RCN319.specialization K f g).toRingHom
  have hdiv : (φ A)^q ∣ φ P := Koala6844Receipts.ClearedForm.specialization_dvd φ A N Q heq q hclear
  have hdegree : (φ P).natDegree < m*S.card+q*(φ A).natDegree := by
    have hpos : 0 < m*a+q*dA := by have := Nat.mul_pos hm ha; omega
    have h := RCN122.specialization_natDegree_lt K (m*a+q*dA) w L B P f g hpos
      (nested_mem_global hbox) hf
    rw [RCN101.specialization_eq_ordinary] at h
    rw [show (φ A).natDegree = dA from hdeg]
    exact h.trans_le (Nat.add_le_add_right (Nat.mul_le_mul_left m hS) _)
  apply Koala6844Receipts.cleared_polynomial_eq_zero x S m q (φ P) (φ A) hdiv hdegree havoid
  intro i hi
  have hh := RCN122.X_pow_dvd_taylor_specialization K P f (x i) (u0 i) (u1 i) g m
      (hvalues i hi) ((contactAtLeast_iff_block_divisibility K (x i) (u0 i) (u1 i) m P).mp (hcontact i hi))
  rw [RCN101.specialization_eq_ordinary] at hh
  exact (RCN185.shifted_power_dvd_iff_taylor_coeff_zero (φ P) (x i) m).mpr
      (Polynomial.X_pow_dvd_iff.mp hh)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
