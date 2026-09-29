import ProximityPrize.SubmissionLower.RelativeCentering

namespace ProximityPrize.SubmissionLower.RelativeBounded6814
open scoped BigOperators
open MvPolynomial RCN119 RCN100 RCN122 ContactOrderBridge
open RelativeContactOrder6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

/-- Regularity bounds the total derivative-contact loss on the actual
agreement set, including nodes where the slope derivative itself vanishes. -/
theorem regular_contact_mass
    {I : Type*} (F : Poly4 K) (hF : F ≠ 0) (f : Polynomial K) (gamma : K)
    (nodes : I ↪ K) (u0 u1 : I → K) (support : Finset I) (w nu : ℕ)
    (hdegree : f.natDegree ≤ w)
    (hweight : MvPolynomial.weightedTotalDegree (RCN081.contactWeights w) F ≤ nu)
    (hregular : specialization K f gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hagrees : ∀ i ∈ support, f.eval (nodes i) = u0 i+gamma*u1 i) :
    (∑ i ∈ support, (contactOrder K (nodes i) (u0 i) (u1 i) F-1)) + w ≤ nu+1 := by
  classical
  let H := MvPolynomial.pderiv (2 : Fin 4) F
  let P := specialization K f gamma H
  have hmult : ∀ i ∈ support,
      contactOrder K (nodes i) (u0 i) (u1 i) F-1 ≤ P.rootMultiplicity (nodes i) := by
    intro i hi
    have hc : ContactAtLeast K (nodes i) (u0 i) (u1 i)
        (contactOrder K (nodes i) (u0 i) (u1 i) F) F :=
      (contactAtLeast_iff_le K _ _ _ _ F hF).mpr le_rfl
    have hd := contactAtLeast_pderiv_R K (nodes i) (u0 i) (u1 i) _ F hc
    have ht := X_pow_dvd_taylor_specialization K H f (nodes i) (u0 i) (u1 i) gamma _
      (hagrees i hi) ((contactAtLeast_iff_block_divisibility K _ _ _ _ H).mp hd)
    apply (Polynomial.le_rootMultiplicity_iff hregular).mpr
    exact (RCN185.shifted_power_dvd_iff_taylor_coeff_zero P (nodes i) _).mpr
      (Polynomial.X_pow_dvd_iff.mp ht)
  have hs : (∑ i ∈ support, (contactOrder K (nodes i) (u0 i) (u1 i) F-1)) ≤ P.natDegree := by
    calc
      _ ≤ ∑ i ∈ support, P.rootMultiplicity (nodes i) := Finset.sum_le_sum hmult
      _ = ∑ a ∈ support.map nodes, P.rootMultiplicity a :=
        (Finset.sum_map support nodes (fun a : K => P.rootMultiplicity a)).symm
      _ ≤ _ := @RCN355.sum_rootMultiplicity_le_natDegree K inferInstance (Classical.decEq K)
        P (support.map nodes)
  have hd := specialized_R_derivative_degree K F f gamma w nu hdegree hweight hregular
  change P.natDegree+w ≤ nu+1 at hd
  omega

theorem affine_order_mass {I : Type*} (support : Finset I) (d : I → ℕ)
    (alpha beta A H : ℕ) (hcard : A ≤ support.card) (hmass : (∑ i ∈ support, d i) ≤ H) :
    alpha*A-beta*H ≤ ∑ i ∈ support, (alpha-beta*d i) := by
  classical
  have hsum : alpha*support.card ≤
      (∑ i ∈ support, (alpha-beta*d i)) + beta*(∑ i ∈ support, d i) := by
    calc
      _ = ∑ _i ∈ support, alpha := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ support, ((alpha-beta*d i)+beta*d i) :=
        Finset.sum_le_sum fun i _ => by omega
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hc := Nat.mul_le_mul_left alpha hcard
  have hm := Nat.mul_le_mul_left beta hmass
  omega

theorem regular_affine_order_mass
    {I : Type*} (F : Poly4 K) (hF : F ≠ 0) (f : Polynomial K) (gamma : K)
    (nodes : I ↪ K) (u0 u1 : I → K) (support : Finset I) (w nu alpha beta A : ℕ)
    (hdegree : f.natDegree ≤ w)
    (hweight : MvPolynomial.weightedTotalDegree (RCN081.contactWeights w) F ≤ nu)
    (hregular : specialization K f gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hagrees : ∀ i ∈ support, f.eval (nodes i) = u0 i+gamma*u1 i)
    (hcard : A ≤ support.card) :
    alpha*A-beta*(nu+1-w) ≤
      ∑ i ∈ support, (alpha-beta*(contactOrder K (nodes i) (u0 i) (u1 i) F-1)) := by
  have hm := regular_contact_mass K F hF f gamma nodes u0 u1 support w nu hdegree hweight
    hregular hagrees
  exact affine_order_mass support _ alpha beta A (nu+1-w) hcard (by omega)

end
end ProximityPrize.SubmissionLower.RelativeBounded6814

#print axioms ProximityPrize.SubmissionLower.RelativeBounded6814.regular_affine_order_mass
