import ProximityPrize.SubmissionLower.RelativeContactInjection
namespace ProximityPrize.SubmissionLower.RelativeContactOrder6814
open scoped BigOperators
open MvPolynomial ContactOrderBridge RCN122
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K]

def RelativeContactAtLeast (x u0 u1 : K) (m : ℕ) (F Q : Poly4 K) : Prop :=
  ∃ B : Poly4 K, ContactAtLeast K x u0 u1 m (Q - F * B)

theorem relative_contact_iff_jet_range
    (x u0 u1 : K) (m : ℕ) (F Q : Poly4 K) (hF : F ≠ 0) :
    RelativeContactAtLeast K x u0 u1 m F Q ↔
      (contactSubmodule K x u0 u1 m).mkQ Q ∈
        LinearMap.range (factorJetMap K x u0 u1 m F hF) := by
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨Submodule.Quotient.mk B,?_⟩
    change (Submodule.Quotient.mk (F*B) : Poly4 K ⧸ contactSubmodule K x u0 u1 m) =
      Submodule.Quotient.mk Q
    symm
    exact (Submodule.Quotient.eq _).mpr hB
  · rintro ⟨q,hq⟩
    obtain ⟨B,rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨B,?_⟩
    apply (Submodule.Quotient.eq (contactSubmodule K x u0 u1 m)).mp
    exact hq.symm

theorem relative_contact_specialization_dvd
    (F Q : Poly4 K) (f : Polynomial K) (x u0 u1 gamma : K) (m : ℕ)
    (hF : specialization K f gamma F = 0)
    (hagrees : f.eval x = u0 + gamma * u1)
    (hcontact : RelativeContactAtLeast K x u0 u1 m F Q) :
    (Polynomial.X - Polynomial.C x)^m ∣ specialization K f gamma Q := by
  obtain ⟨B,hB⟩ := hcontact
  have ht := X_pow_dvd_taylor_specialization K (Q-F*B) f x u0 u1 gamma m hagrees
    ((contactAtLeast_iff_block_divisibility K x u0 u1 m (Q-F*B)).mp hB)
  simp only [map_sub, map_mul, hF, zero_mul, sub_zero] at ht
  exact (RCN185.shifted_power_dvd_iff_taylor_coeff_zero
    (specialization K f gamma Q) x m).mpr (Polynomial.X_pow_dvd_iff.mp ht)

theorem relative_contact_specialization_eq_zero
    {I : Type*} (F Q : Poly4 K) (f : Polynomial K) (gamma : K)
    (nodes : I ↪ K) (u0 u1 : I → K) (support : Finset I) (m : I → ℕ)
    (hF : specialization K f gamma F = 0)
    (hagrees : ∀ i ∈ support, f.eval (nodes i) = u0 i + gamma * u1 i)
    (hcontact : ∀ i ∈ support,
      RelativeContactAtLeast K (nodes i) (u0 i) (u1 i) (m i) F Q)
    (hdegree : (specialization K f gamma Q).natDegree < ∑ i ∈ support, m i) :
    specialization K f gamma Q = 0 := by
  classical
  by_contra hne
  have hmult : ∀ i ∈ support, m i ≤
      (specialization K f gamma Q).rootMultiplicity (nodes i) := by
    intro i hi
    apply (Polynomial.le_rootMultiplicity_iff hne).mpr
    exact relative_contact_specialization_dvd K F Q f
      (nodes i) (u0 i) (u1 i) gamma (m i) hF (hagrees i hi) (hcontact i hi)
  have hsum : (∑ i ∈ support, m i) ≤ (specialization K f gamma Q).natDegree := by
    calc
      _ ≤ ∑ i ∈ support, (specialization K f gamma Q).rootMultiplicity (nodes i) :=
        Finset.sum_le_sum hmult
      _ = ∑ a ∈ support.map nodes, (specialization K f gamma Q).rootMultiplicity a :=
        (Finset.sum_map support nodes
          (fun a : K => (specialization K f gamma Q).rootMultiplicity a)).symm
      _ ≤ _ := @RCN355.sum_rootMultiplicity_le_natDegree K inferInstance (Classical.decEq K)
        (specialization K f gamma Q) (support.map nodes)
  omega

end
end ProximityPrize.SubmissionLower.RelativeContactOrder6814
