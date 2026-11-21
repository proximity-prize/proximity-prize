import ProximityPrize.SubmissionLower.Rect51HilbertProfiles

set_option autoImplicit false
set_option Elab.async false

namespace Rect51Hilbert
noncomputable section
open K1_14 (FX Seeds Equation)
open HighCore82706Tangent_3 (JetRing ordinate seedVar)
open MvPolynomial
open scoped BigOperators

private abbrev Exponents (d : Degree) :=
  {m : CoxVar →₀ ℕ // Finsupp.weight coxWeight m = d}
private theorem coordinates {d : Degree} (m : Exponents d) :
    m.val h₀ + m.val h₁ + 2*m.val v₁ = d.1 ∧
    m.val v₀ + m.val v₁ = d.2.1 ∧
    m.val (seed₀ 0) + m.val (seed₀ 1) = d.2.2.1 ∧
    m.val (seed₁ 0) + m.val (seed₁ 1) = d.2.2.2 := by
  have hm := m.property
  rw [weight_coordinates] at hm
  exact ⟨congrArg Prod.fst hm, congrArg (fun x : Degree => x.2.1) hm,
    congrArg (fun x : Degree => x.2.2.1) hm, congrArg (fun x : Degree => x.2.2.2) hm⟩
private theorem exponent_ext {m n : Exponent}
    (ha : m h₀ = n h₀) (hb : m h₁ = n h₁) (hc : m v₀ = n v₀) (hd : m v₁ = n v₁)
    (hs₀ : ∀ i, m (seed₀ i) = n (seed₀ i)) (hs₁ : ∀ i, m (seed₁ i) = n (seed₁ i)) : m = n := by
  apply Finsupp.ext
  intro i
  rcases i with i | (i | (i | i))
  · fin_cases i
    · exact ha
    · exact hb
  · fin_cases i
    · exact hc
    · exact hd
  · exact hs₀ i
  · exact hs₁ i
private def seedLift : Seeds →+* Cox :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X (if i = 0 then seed₀ 1 else seed₁ 1))
private def rootLift : Equation →+* Cox :=
  Polynomial.eval₂RingHom seedLift (MvPolynomial.X h₁)
private def affineLift : JetRing →+* Cox :=
  Polynomial.eval₂RingHom rootLift (MvPolynomial.X v₁)
private def kept : CoxVar → Prop
  | .inl i => i ≠ 0
  | .inr (.inl i) => i ≠ 0
  | .inr (.inr (.inl i)) => i ≠ 0
  | .inr (.inr (.inr i)) => i ≠ 0
private def surviving (m : CoxVar →₀ ℕ) : CoxVar →₀ ℕ := by
  classical
  exact m.filter kept
open scoped Classical in
private theorem lift_coord (i : CoxVar) :
    affineLift (affineCoord i) = if kept i then MvPolynomial.X i else 1 := by
  rcases i with i | (i | (i | i)) <;> fin_cases i <;>
    simp [affineCoord, affineLift, rootLift, seedLift, kept, ordinate, seedVar, h₁, v₁, seed₀, seed₁]
private theorem lift_monomial (m : CoxVar →₀ ℕ) (a : FX) :
    affineLift (dehom (monomial m a)) = monomial (surviving m) a := by
  classical
  have ha : affineLift (algebraMap FX JetRing a) = MvPolynomial.C a := by
    change affineLift (Polynomial.C (Polynomial.C (MvPolynomial.C a))) = MvPolynomial.C a
    simp [affineLift, rootLift, seedLift]
  conv_rhs => rw [monomial_eq]
  rw [dehom, aeval_monomial, map_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ha]
  apply congrArg (fun p : Cox => MvPolynomial.C a * p)
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow, lift_coord]
  by_cases hi : kept i <;> simp [surviving, hi]
private theorem surviving_injective (d : Degree) :
    Function.Injective (fun m : Exponents d => surviving m.val) := by
  intro m n he
  have same (i : CoxVar) (hi : kept i) : m.val i = n.val i := by
    simpa only [surviving, Finsupp.filter_apply, ite_eq_left hi] using
      DFunLike.congr_fun he i
  have hh := same h₁ (by change (1 : Fin 2) ≠ 0; decide)
  have hv := same v₁ (by change (1 : Fin 2) ≠ 0; decide)
  have hs₀ := same (seed₀ 1) (by change (1 : Fin 2) ≠ 0; decide)
  have hs₁ := same (seed₁ 1) (by change (1 : Fin 2) ≠ 0; decide)
  obtain ⟨hm₁, hm₂, hm₃, hm₄⟩ := coordinates m
  obtain ⟨hn₁, hn₂, hn₃, hn₄⟩ := coordinates n
  apply Subtype.ext
  refine exponent_ext (by omega) hh (by omega) hv (fun i => ?_) (fun i => ?_)
  · fin_cases i
    · change m.val (seed₀ 0) = n.val (seed₀ 0)
      omega
    · exact hs₀
  · fin_cases i
    · change m.val (seed₁ 0) = n.val (seed₁ 0)
      omega
    · exact hs₁
private theorem coeff_lift {d : Degree} {p : Cox} (hp : p.IsWeightedHomogeneous coxWeight d)
    (m : Exponents d) : (affineLift (dehom p)).coeff (surviving m.val) = p.coeff m.val := by
  classical
  conv_rhs => rw [p.as_sum, coeff_sum]
  conv_lhs => rw [p.as_sum, map_sum, map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := hp (mem_support_iff.mp hn)
  have he : surviving n = surviving m.val ↔ n = m.val :=
    ⟨fun h => congrArg Subtype.val (surviving_injective d (a₁ := ⟨n, hn'⟩) (a₂ := m) h),
      congrArg surviving⟩
  simp only [lift_monomial, coeff_monomial, he]
private theorem dehom_eq_of_degree {d : Degree} {p q : Cox}
    (hp : p.IsWeightedHomogeneous coxWeight d) (hq : q.IsWeightedHomogeneous coxWeight d)
    (he : dehom p = dehom q) : p = q := by
  apply MvPolynomial.ext
  intro m
  by_cases hm : Finsupp.weight coxWeight m = d
  · rw [← coeff_lift hp ⟨m, hm⟩, ← coeff_lift hq ⟨m, hm⟩, he]
  · have hp₀ : p.coeff m = 0 := by by_contra h; exact hm (hp h)
    have hq₀ : q.coeff m = 0 := by by_contra h; exact hm (hq h)
    rw [hp₀, hq₀]
private theorem ambient_rank (d : Degree) :
    Module.finrank FX (gradedPiece ⊥ d) = Nat.card (Exponents d) := by
  let S := homogeneous d
  let f := (qmap (⊥ : Ideal JetRing)).toLinearMap
  let g : S →ₗ[FX] gradedPiece ⊥ d :=
    (f.comp S.subtype).codRestrict _ (fun p => Submodule.mem_map.mpr ⟨p.val, p.prop, rfl⟩)
  have hg : Function.Bijective g := by
    constructor
    · intro p q he
      apply Subtype.ext
      apply dehom_eq_of_degree p.prop q.prop
      have he' : Ideal.Quotient.mk ⊥ (dehom p.val) = Ideal.Quotient.mk ⊥ (dehom q.val) :=
        congrArg Subtype.val he
      simpa only [RingEquiv.quotientBot_mk] using congrArg (RingEquiv.quotientBot JetRing) he'
    · intro q
      obtain ⟨p, hp, he⟩ := Submodule.mem_map.mp q.prop
      exact ⟨⟨p, hp⟩, Subtype.ext he⟩
  rw [← (LinearEquiv.ofBijective g hg).finrank_eq]
  change Module.finrank FX (weightedHomogeneousSubmodule FX coxWeight d) = _
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport FX {m | Finsupp.weight coxWeight m = d})
theorem ambient_profile : IsProfile (⊥ : Ideal JetRing) ambient := by
  refine ⟨1, fun h t s₀ s₁ hh ht hs₀ hs₁ => ?_⟩
  change (hilbert ⊥ h t s₀ s₁ : ℚ) = _
  rw [hilbert, ambient_rank]
  change (Nat.card (↥({m : Exponent | Finsupp.weight coxWeight m = nefDegree h t s₀ s₁} : Set Exponent)) : ℚ) = _
  rw [Nat.card_coe_set_eq]
  simpa only [exponentCount, Set.mem_univ, true_and] using ambient_count h t s₀ s₁ hh ht hs₀ hs₁

#print axioms ambient_profile
end
end Rect51Hilbert
