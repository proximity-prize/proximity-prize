import ProximityPrize.SubmissionLower.Koala6844VirtualShortPhysical


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetWeightedSupport SecondJetCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2900000

variable {K : Type*} [Field K]

private def weights (w : ℕ) : Fin 5 → ℤ := ![1,((w-2 : ℕ):ℤ),w,((w-1 : ℕ):ℤ),0]

def sourceWeight (w : ℕ) (e : Fin 5 →₀ ℕ) : ℕ := e 0+w*e 2+(w-1)*e 3+(w-2)*e 1

private theorem weight_eq (w : ℕ) (e : Fin 5 →₀ ℕ) :
    weight (weights w) e = (sourceWeight w e : ℤ) := by
  rw [weight, Fin.sum_univ_five]
  change (e 0 : ℤ)*1+(e 1 : ℤ)*((w-2 : ℕ):ℤ)+(e 2 : ℤ)*(w : ℤ)+
    (e 3 : ℤ)*((w-1 : ℕ):ℤ)+(e 4 : ℤ)*0 = (sourceWeight w e : ℤ)
  simp only [sourceWeight,Nat.cast_add,Nat.cast_mul]
  ring

private theorem linear_const (w : Fin 5 → ℤ) (b : K) :
    LinearBound w 0 (MvPolynomial.C b : Poly (K := K)) := by
  intro e he
  have hz := Finset.mem_singleton.mp (MvPolynomial.support_C_subset he)
  subst e
  simp [weight]

private theorem linear_sum {ι : Type*} (w : Fin 5 → ℤ) (b : ℤ)
    (v : Finset ι) (f : ι → Poly (K := K))
    (hf : ∀ i ∈ v, LinearBound w b (f i)) : LinearBound w b (∑ i ∈ v, f i) := by
  classical
  induction v using Finset.induction_on with
  | empty => simp [LinearBound]
  | insert i v hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf _ (Finset.mem_insert_self _ _)).add (ih (fun j hj => hf _ (Finset.mem_insert_of_mem hj)))

private theorem linear_embed (w : ℕ) (p : Polynomial K) :
    LinearBound (weights w) p.natDegree (embedDisplacement p) := by
  classical
  have h : embedDisplacement p =
       ∑ i ∈ p.support, MvPolynomial.C (p.coeff i)*MvPolynomial.X 0^i := by
    conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow p]
    simp [embedDisplacement]
  rw [h]
  apply linear_sum
  intro i hi
  have hm := (linear_const (weights w) (p.coeff i)).mul ((linear_X (K := K) (weights w) 0).pow i)
  have hi' := Polynomial.le_natDegree_of_mem_supp i hi
  have hi'' : (i : ℤ) ≤ (p.natDegree : ℤ) := by exact_mod_cast hi'
  apply hm.mono
  simpa [weights] using hi''

private theorem linear_den (w a : ℕ) (A₀ A₁ : Polynomial K)
    (h₀ : A₀.natDegree ≤ a) (h₁ : A₁.natDegree ≤ a) :
    LinearBound (weights w) a (normalizedDenominator A₀ A₁) := by
  unfold normalizedDenominator
  apply ((linear_embed w A₀).mono (by exact_mod_cast h₀)).add
  apply ((linear_embed w A₁).mul (linear_X (K := K) (weights w) 4)).mono
  simpa [weights] using (show (A₁.natDegree : ℤ) ≤ (a : ℤ) by exact_mod_cast h₁)

private theorem linear_num (w a wQ : ℕ) (d C₁ : Polynomial K)
    (hd : d.natDegree+w ≤ a+wQ) (hC : C₁.natDegree ≤ a+wQ) :
    LinearBound (weights w) ((a : ℤ)+(wQ : ℤ)) (normalizedNumerator d C₁) := by
  unfold normalizedNumerator
  apply LinearBound.add
  · apply ((linear_embed w d).mul (linear_X (K := K) (weights w) 2)).mono
    simpa [weights] using (show (d.natDegree : ℤ)+(w : ℤ) ≤ (a : ℤ)+(wQ : ℤ) by exact_mod_cast hd)
  · apply ((linear_embed w C₁).mul (linear_X (K := K) (weights w) 4)).mono
    simpa [weights] using (show (C₁.natDegree : ℤ) ≤ (a : ℤ)+(wQ : ℤ) by exact_mod_cast hC)

theorem clear_normalized_weight (A₀ A₁ d C₁ : Polynomial K) (w wQ a q D : ℕ)
    (h₀ : A₀.natDegree ≤ a) (h₁ : A₁.natDegree ≤ a)
    (hd : d.natDegree+w ≤ a+wQ) (hC : C₁.natDegree ≤ a+wQ)
    (P : Polynomial (Poly (K := K)))
    (hP : ∀ j e, e ∈ (P.coeff j).support → sourceWeight w e+wQ*j < D) :
    ∀ e ∈ (clearAux (normalizedDenominator A₀ A₁) (normalizedNumerator d C₁) q P).support,
      sourceWeight w e < D+q*a := by
  classical
  let A := normalizedDenominator A₀ A₁
  let N := normalizedNumerator d C₁
  let b := (D : ℤ) - 1 + (q : ℤ)*(a : ℤ)
  have hbound : LinearBound (weights w) b (clearAux A N q P) := by
    unfold clearAux
    apply linear_sum (weights w) b (Finset.range (q+1))
      (fun j => A^(q-j)*(P.coeff j*N^j))
    intro j hj
    have hjq : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hc : LinearBound (weights w) ((D : ℤ)-1-(wQ : ℤ)*(j : ℤ)) (P.coeff j) := by
      intro e he
      rw [weight_eq]
      have he' : (sourceWeight w e : ℤ)+(wQ : ℤ)*(j : ℤ) < (D : ℤ) := by
        exact_mod_cast hP j e he
      omega
    apply (((linear_den w a A₀ A₁ h₀ h₁).pow (q-j)).mul
      (hc.mul ((linear_num w a wQ d C₁ hd hC).pow j))).mono
    unfold b
    rw [Nat.cast_sub hjq]
    ring_nf
    exact le_rfl
  intro e he
  have hh := hbound e he
  rw [weight_eq] at hh
  have hx : (sourceWeight w e : ℤ) < ((D+q*a : ℕ):ℤ) := by
    simp only [b,Nat.cast_add,Nat.cast_mul] at hh ⊢
    omega
  exact_mod_cast hx

theorem firstJet_coefficient_weight (P : Poly (K := K)) (w D : ℕ)
    (hP : ∀ e ∈ P.support, sourceWeight w e < D) :
    ∀ e ∈ ((asS P).coeff 0).support, e 0+w*e 1+(w-1)*e 2 < D := by
  intro e he
  have h := hP _ (coefficient_support P 0 e he)
  obtain ⟨h0,h1,h2,h3,_⟩ := lift_coordinates 0 e
  simpa only [sourceWeight,h0,h1,h2,h3,Nat.mul_zero,Nat.add_zero] using h

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
