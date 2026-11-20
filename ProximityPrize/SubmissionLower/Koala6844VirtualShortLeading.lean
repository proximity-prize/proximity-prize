import ProximityPrize.SubmissionLower.Koala6844VirtualShortVanish


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
open SecondJetSpecialize SecondJetRelaxedDifferentiation
open SecondJetCoefficients SecondJetCoefficientSpecialization

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {K N : Type*} [Field K]

private abbrev Aux (K : Type*) [Field K] :=
  Polynomial (Poly (K := K))

def jetSlice (P : Aux K) (h : ℕ) : Polynomial (MvPolynomial (Fin 4) K) :=
  P.sum fun j c => Polynomial.monomial j ((asS c).coeff h)

@[simp]
theorem jetSlice_coeff (P : Aux K) (h j : ℕ) :
    (jetSlice P h).coeff j = (asS (P.coeff j)).coeff h := by
  classical
  unfold jetSlice Polynomial.sum
  rw [Polynomial.finsetSum_coeff]
  by_cases hmem : j ∈ P.support
  · rw [Finset.sum_eq_single_of_mem j hmem]
    · simp
    · intro i _ hi
      simp [Polynomial.coeff_monomial, hi]
  · have hz := Polynomial.notMem_support_iff.mp hmem
    rw [hz, map_zero, Polynomial.coeff_zero]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : i ≠ j := fun hh => hmem (hh ▸ hi)
    simp [Polynomial.coeff_monomial, hne]

theorem clearAux_asS_coeff (P : Aux K) (A B : Poly (K := K))
    (A₀ B₀ : MvPolynomial (Fin 4) K) (q h : ℕ)
    (hA : asS A = Polynomial.C A₀) (hB : asS B = Polynomial.C B₀) :
    (asS (clearAux A B q P)).coeff h = clearAux A₀ B₀ q (jetSlice P h) := by
  unfold clearAux
  rw [map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, map_pow, hA, map_mul, map_pow, hB, ← Polynomial.C_pow,
    ← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, jetSlice_coeff]

theorem jet_index_le_cleared_degree (P : Aux K) (A B : Poly (K := K))
    (A₀ B₀ : MvPolynomial (Fin 4) K) (q : ℕ)
    (hA : asS A = Polynomial.C A₀) (hB : asS B = Polynomial.C B₀)
    (hinj : ∀ h, clearAux A₀ B₀ q (jetSlice P h) = 0 → jetSlice P h = 0)
    (j : ℕ) (e : Fin 5 →₀ ℕ) (he : e ∈ (P.coeff j).support) :
    e 1 ≤ (asS (clearAux A B q P)).natDegree := by
  let d : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![e 0, e 2, e 3, e 4]
  have hlift : liftExponent (e 1) d = e := by
    obtain ⟨h0, h1, h2, h3, h4⟩ := lift_coordinates (e 1) d
    ext i
    fin_cases i <;> simp [d, h0, h1, h2, h3, h4]
  apply Polynomial.le_natDegree_of_ne_zero
  intro hzero
  rw [clearAux_asS_coeff P A B A₀ B₀ q (e 1) hA hB] at hzero
  have hs := congrArg (fun F : Polynomial (MvPolynomial (Fin 4) K) => F.coeff j)
    (hinj (e 1) hzero)
  rw [jetSlice_coeff, Polynomial.coeff_zero] at hs
  have hc := congrArg (fun F : MvPolynomial (Fin 4) K => AddMonoidAlgebra.coeff F d) hs
  rw [asS_coeff, hlift] at hc
  exact (MvPolynomial.mem_support_iff.mp he) (by simpa using hc)

private theorem iterate_derivative_top {R : Type*} [CommRing R] (P : Polynomial R) (d : ℕ)
    (hh : ∀ j, d < j → P.coeff j = 0) :
    (Polynomial.derivative)^[d] P = Polynomial.C (d.factorial • P.coeff d) := by
  ext j
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hj : j = 0
  · subst j
    simp [Nat.descFactorial_self]
  · rw [hh (j+d) (by omega)]
    simp [hj]

private theorem specialize_top (P : Poly (K := K)) (f : Polynomial K) (z : K) (d : ℕ)
    (hdeg : (asS P).natDegree = d) :
    specialize f z ((MvPolynomial.pderiv 1)^[d] P) =
      d.factorial • coefficientSpecialize f z ((asS P).coeff d) := by
  rw [specialize_eq, asS_iterate, ← Polynomial.eval_map, ← Polynomial.iterate_derivative_map]
  rw [iterate_derivative_top _ d (by
    intro j hj
    rw [Polynomial.coeff_map, Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg ▸ hj), map_zero])]
  simp

theorem normalized_leading_coefficient_vanish
    (P : Aux K) (A B : Poly (K := K)) (m a w wQ k n0 q d : ℕ)
    (ha : 0 < a) (hwa : w-2 ≤ a) (hdm : d < m) (hdn : d < n0)
    (hfact : (d.factorial : K) ≠ 0)
    (hdegree : P.natDegree ≤ q)
    (hjet : ∀ j e, e ∈ (P.coeff j).support → e 1 ≤ d)
    (hleading : (asS (clearAux A B q P)).natDegree = d)
    (hA : MvPolynomial.pderiv 1 A = 0) (hB : MvPolynomial.pderiv 1 B = 0)
    (hweight : ∀ j e, e ∈ (P.coeff j).support →
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+wQ*j+
        reserve k n0 (e 1)*(a-(w-2)) < m*a)
    (nodes : N ↪ K) (u0 u1 : N → K)
    (f Q : Polynomial K) (hf : f.natDegree ≤ w) (hQ : Q.natDegree ≤ wQ)
    (z : K) (S : Finset N) (hS : a ≤ S.card)
    (hagree : ∀ i ∈ S, f.eval (nodes i) = u0 i + u1 i*z)
    (hden : ∀ i ∈ S, (specialize f z A).eval (nodes i) ≠ 0)
    (hequation : specialize f z B = specialize f z A * Q)
    (hcontact : ∀ i ∈ S, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) (clearAux A B q P))) :
    coefficientSpecialize f z ((asS (clearAux A B q P)).leadingCoeff) = 0 := by
  have hreserve (j : ℕ) (e : Fin 5 →₀ ℕ) (he : e ∈ (P.coeff j).support)
      (hde : d ≤ e 1) : d ≤ reserve k n0 (e 1) := by
    have h₁ := hjet j e he
    have he' : e 1 = d := Nat.le_antisymm h₁ hde
    simp [he', reserve, hdn]
  have hv := normalized_derivative_vanish P A B m a w wQ k n0 q d ha hwa hdm
    hdegree hA hB hweight hreserve nodes u0 u1 f Q hf hQ z S hS hagree hden hequation hcontact
  rw [specialize_top _ f z d hleading, nsmul_eq_mul] at hv
  have hn : (d.factorial : Polynomial K) ≠ 0 := by
    simpa only [map_natCast] using (Polynomial.C_ne_zero.mpr hfact)
  simpa only [← hleading, Polynomial.coeff_natDegree] using (mul_eq_zero.mp hv).resolve_left hn

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
