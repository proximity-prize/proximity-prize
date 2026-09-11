import ProximityPrize.SubmissionLower.Part.G066


section Compact_SecondJetWeightedBasis
/-! Independence of the U/J/V family with J powers selected per monomial.
This proves independence only. Finite support and counting remain separate. -/
namespace ProximityPrize.SubmissionLower.SecondJetWeightedBasis
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetRank SecondJetLocal
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem C_smul_base (c : K) (v : Base (K := K)) :
    Polynomial.C (c • v) = c • (Polynomial.C v : Polynomial (Base (K := K))) :=
  map_smul (Polynomial.CAlgHom (R := K) (A := Base (K := K))) c v

/-- The inner polynomial variable is S and the outer variable is epsilon. -/
def weightedTerm (r h a b : ℕ) (e : Fin 3 →₀ ℕ) : Jet (Base (K := K)) :=
  SecondJetWeightedContact.family
    (Polynomial.C (MvPolynomial.X 0)) (Polynomial.C (MvPolynomial.X 1))
    Polynomial.X (Polynomial.C (MvPolynomial.X 2^(e 2)))
    r h a b (e 0) (e 1) (min a (e 1))

theorem weightedTerm_coeff_lt (r h a b : ℕ) (e : Fin 3 →₀ ℕ)
    (d : ℕ) (hd : d < r) : (weightedTerm (K := K) r h a b e).coeff d = 0 :=
  SecondJetWeightedContact.family_coeff_lt _ _ _ _ _ _ _ _ _ _ _ _ hd

theorem weightedTerm_coeff_self (r h a b : ℕ) (e : Fin 3 →₀ ℕ) :
    (weightedTerm (K := K) r h a b e).coeff r = Polynomial.X^h *
      Polynomial.C (SecondJetLocal.v^(a+b)*MvPolynomial.monomial e (1 : K)) := by
  rw [weightedTerm, SecondJetWeightedContact.family_coeff_self _ _ _ _ _ _ _ _ _ _ _
    (min_le_left _ _) (min_le_right _ _)]
  have hm : MvPolynomial.monomial e (1 : K) =
      MvPolynomial.X 0^(e 0)*MvPolynomial.X 1^(e 1)*MvPolynomial.X 2^(e 2) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    · simp [Fin.prod_univ_three]
    · intro i; simp
  rw [hm]
  simp only [SecondJetLocal.v, map_sub, map_mul, map_pow, mul_assoc]

variable {m s : ℕ} {I : Fin m → Fin s → Type*} [∀ r h, Fintype (I r h)]
abbrev Parameters := ∀ r : Fin m, ∀ h : Fin s, I r h → K

def weightedMake (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) : Parameters (K := K) (I := I) →ₗ[K] Jet (Base (K := K)) :=
  ∑ r, ∑ h, ∑ i, LinearMap.smulRight
    (((LinearMap.proj i : (I r h → K) →ₗ[K] K).comp
      (LinearMap.proj h : (∀ h, I r h → K) →ₗ[K] (I r h → K))).comp (LinearMap.proj r : Parameters (K := K) (I := I) →ₗ[K] (∀ h, I r h → K)))
    (weightedTerm r.val h.val (a r h) (b r h) (e r h i))

theorem weightedMake_apply (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (p : Parameters (K := K) (I := I)) :
    weightedMake a b e p = ∑ r, ∑ h, ∑ i,
      p r h i • weightedTerm r.val h.val (a r h) (b r h) (e r h i) := by
  simp [weightedMake]

theorem weightedMake_initial (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (p : Parameters (K := K) (I := I)) (r : Fin m)
    (hp : ∀ j, j.val < r.val → p j = 0) :
    (weightedMake a b e p).coeff r.val = ∑ h, Polynomial.X^h.val *
      Polynomial.C (SecondJetLocal.v^(a r h+b r h)*FiniteMonomials.reconstruct (e r h) (p r h)) := by
  rw [weightedMake_apply, Polynomial.finsetSum_coeff, Finset.sum_eq_single r]
  · simp_rw [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, weightedTerm_coeff_self]
    apply Finset.sum_congr rfl
    intro h _
    rw [FiniteMonomials.reconstruct_apply, Finset.mul_sum, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hm : MvPolynomial.monomial (e r h i) (p r h i) =
        p r h i • MvPolynomial.monomial (e r h i) (1 : K) := by
      simpa only [smul_eq_mul, mul_one] using
        (map_smul (MvPolynomial.monomial (e r h i)) (p r h i) (1 : K))
    rw [hm]
    simp only [mul_smul_comm, C_smul_base]
  · intro j _ hj
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro i _
    by_cases hlt : j.val < r.val
    · simp [hp j hlt]
    · rw [weightedTerm_coeff_lt]
      · simp
      · have hne : j.val ≠ r.val := fun he => hj (Fin.ext he)
        omega
  · simp

theorem truncate_weightedMake_initial (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (p : Parameters (K := K) (I := I)) (r : Fin m)
    (hp : ∀ j, j.val < r.val → p j = 0) :
    truncate (K := K) (m := m) (s := s) (weightedMake a b e p) r =
      fun h => SecondJetLocal.v^(a r h+b r h)*FiniteMonomials.reconstruct (e r h) (p r h) := by
  funext h
  rw [truncate_apply, weightedMake_initial a b e p r hp, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_mul_C, Polynomial.coeff_X_pow, Fin.val_inj]
  simp

theorem truncate_weightedMake_injective (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (he : ∀ r h, Function.Injective (e r h)) :
    Function.Injective ((truncate (K := K) (m := m) (s := s)).comp (weightedMake a b e)) := by
  let D : ∀ r : Fin m, (∀ h : Fin s, I r h → K) →ₗ[K] (Fin s → Base (K := K)) := fun r =>
    LinearMap.pi (fun h => (LinearMap.mulLeft K (SecondJetLocal.v^(a r h+b r h))).comp
      ((FiniteMonomials.reconstruct (e r h)).comp (LinearMap.proj h)))
  apply TriangularKernel.injective_of_triangular _ D
  · intro r p q hpq
    funext h i
    have hh := congrFun hpq h
    change SecondJetLocal.v^(a r h+b r h)*FiniteMonomials.reconstruct (e r h) (p h) =
      SecondJetLocal.v^(a r h+b r h)*FiniteMonomials.reconstruct (e r h) (q h) at hh
    have hz := mul_left_cancel₀ (pow_ne_zero _ (SecondJetLocal.v_ne_zero (K := K))) hh
    exact congrFun (FiniteMonomials.reconstruct_injective (e r h) (he r h) hz) i
  · intro p r hp
    exact truncate_weightedMake_initial a b e p r hp

theorem truncateOuter_weightedMake_injective (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (he : ∀ r h, Function.Injective (e r h)) :
    Function.Injective ((truncateOuter (K := K) m).comp (weightedMake a b e)) := by
  intro p q hpq
  apply truncate_weightedMake_injective a b e he
  have hh := congrArg (truncate (K := K) (m := m) (s := s)) hpq
  simpa only [LinearMap.comp_apply, truncate_truncateOuter] using hh

/-- Every concretely embedded and vanishing instance of this independent family
saves its full cardinality in the local rank bound. -/
theorem finite_source_rank {T : Type*} [AddCommGroup T] [Module K T]
    (W : Submodule K (Jet (Base (K := K)))) [FiniteDimensional K W]
    (f : W →ₗ[K] T) (a b : Fin m → Fin s → ℕ)
    (e : ∀ r h, I r h → Fin 3 →₀ ℕ) (he : ∀ r h, Function.Injective (e r h))
    (hW : ∀ p, truncateOuter (K := K) m (weightedMake a b e p) ∈ W)
    (hzero : ∀ p, f ⟨truncateOuter (K := K) m (weightedMake a b e p), hW p⟩ = 0) :
    Module.finrank K f.range + (∑ r : Fin m, ∑ h : Fin s, Fintype.card (I r h)) ≤
      Module.finrank K W := by
  let g := (truncateOuter (K := K) m).comp (weightedMake a b e)
  have hg : Function.Injective g := truncateOuter_weightedMake_injective a b e he
  let gw : Parameters (K := K) (I := I) →ₗ[K] W := g.codRestrict W hW
  let gk : Parameters (K := K) (I := I) →ₗ[K] f.ker := gw.codRestrict f.ker hzero
  have hi : Function.Injective gk := by
    intro p q hpq
    apply hg
    exact congrArg (fun x : f.ker => (x.val : Jet (Base (K := K)))) hpq
  letI : AddCommGroup W := inferInstance
  letI : Module K W := W.module
  letI : FiniteDimensional K f.ker := inferInstance
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have hsum := f.finrank_range_add_finrank_ker
  have hd : Module.finrank K (Parameters (K := K) (I := I)) =
      ∑ r : Fin m, ∑ h : Fin s, Fintype.card (I r h) := by
    simp [Parameters, Module.finrank_pi_fintype]
  rw [hd] at hdim
  omega

end
end ProximityPrize.SubmissionLower.SecondJetWeightedBasis

end Compact_SecondJetWeightedBasis
