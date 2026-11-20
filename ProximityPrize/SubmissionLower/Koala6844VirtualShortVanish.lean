import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.Koala6844VirtualShortClear


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation
open SecondJetSpecialize SecondJetRelaxedDifferentiation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {K N : Type*} [Field K]

private abbrev Source (K : Type*) [Field K] :=
  Polynomial (Poly (K := K))

def derivativeAux (P : Source K) : Source K :=
  P.sum fun j c => Polynomial.monomial j (MvPolynomial.pderiv 1 c)

@[simp]
theorem derivativeAux_coeff (P : Source K) (j : ℕ) :
    (derivativeAux P).coeff j = MvPolynomial.pderiv 1 (P.coeff j) := by
  classical
  unfold derivativeAux Polynomial.sum
  rw [Polynomial.finsetSum_coeff]
  by_cases h : j ∈ P.support
  · rw [Finset.sum_eq_single_of_mem j h]
    · simp
    · intro i _ hi
      simp [Polynomial.coeff_monomial, hi]
  · have hz := Polynomial.notMem_support_iff.mp h
    rw [hz, map_zero]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : i ≠ j := fun hh => h (hh ▸ hi)
    simp [Polynomial.coeff_monomial, hne]

@[simp]
theorem iterate_derivativeAux_coeff (P : Source K) (j d : ℕ) :
    ((derivativeAux^[d]) P).coeff j =
      ((MvPolynomial.pderiv 1)^[d]) (P.coeff j) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      derivativeAux_coeff, ih]

theorem iterate_derivativeAux_natDegree_le (P : Source K) (d : ℕ) :
    ((derivativeAux^[d]) P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [iterate_derivativeAux_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hj]
  induction d with
  | zero => rfl
  | succ d ih => simp only [Function.iterate_succ_apply', ih, map_zero]

theorem pderiv_clearAux (A B : Poly (K := K)) (q : ℕ) (P : Source K)
    (hA : MvPolynomial.pderiv 1 A = 0) (hB : MvPolynomial.pderiv 1 B = 0) :
    MvPolynomial.pderiv 1 (clearAux A B q P) = clearAux A B q (derivativeAux P) := by
  unfold clearAux
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [derivativeAux_coeff, Derivation.leibniz, Derivation.leibniz_pow, hA, hB, mul_comm]

theorem iterate_pderiv_clearAux (A B : Poly (K := K)) (q d : ℕ) (P : Source K)
    (hA : MvPolynomial.pderiv 1 A = 0) (hB : MvPolynomial.pderiv 1 B = 0) :
    ((MvPolynomial.pderiv 1)^[d]) (clearAux A B q P) =
      clearAux A B q ((derivativeAux^[d]) P) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      pderiv_clearAux A B q _ hA hB]

def auxiliaryEvaluation (f Q : Polynomial K) (z : K) (P : Source K) :
    Polynomial K :=
  (P.map (specialize f z).toRingHom).eval Q

theorem specialize_clearAux (A B : Poly (K := K)) (q : ℕ) (P : Source K)
    (f Q : Polynomial K) (z : K) (hdegree : P.natDegree ≤ q)
    (hequation : specialize f z B = specialize f z A * Q) :
    specialize f z (clearAux A B q P) =
      (specialize f z A)^q * auxiliaryEvaluation f Q z P := by
  change (specialize f z).toRingHom (clearAux A B q P) = _
  rw [clearAux_map]
  change clearAux (specialize f z A) (specialize f z B) q
    (P.map (specialize f z).toRingHom) = _
  rw [hequation, clearAux_mul_normalized _ _ _ _ (Polynomial.natDegree_map_le.trans hdegree)]
  rfl

private theorem auxiliaryTerm_degree_lt (f Q : Polynomial K) (z : K)
    (w wQ j D : ℕ) (hf : f.natDegree ≤ w) (hQ : Q.natDegree ≤ wQ)
    (hD : 0 < D) (p : Poly (K := K))
    (hp : ∀ e ∈ p.support, e 0 + w*e 2 + (w-1)*e 3 + (w-2)*e 1 + wQ*j < D) :
    (specialize f z p * Q^j).natDegree < D := by
  classical
  have hpow := Polynomial.natDegree_pow_le_of_le j hQ
  rw [MvPolynomial.as_sum p, map_sum, Finset.sum_mul]
  refine (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_).trans_lt (by omega : D-1 < D)
  intro e he
  have hm := SecondJetSpecialize.monomial_degree f z w hf e (AddMonoidAlgebra.coeff p e)
  have hp' := hp e he
  have hmul := Polynomial.natDegree_mul_le_of_le hm hpow
  exact hmul.trans (by rw [Nat.mul_comm j wQ] at hmul ⊢
                       omega)

theorem auxiliaryEvaluation_degree_lt (f Q : Polynomial K) (z : K) (P : Source K)
    (w wQ D : ℕ) (hf : f.natDegree ≤ w) (hQ : Q.natDegree ≤ wQ) (hD : 0 < D)
    (hP : ∀ j e, e ∈ (P.coeff j).support →
      e 0 + w*e 2 + (w-1)*e 3 + (w-2)*e 1 + wQ*j < D) :
    (auxiliaryEvaluation f Q z P).natDegree < D := by
  classical
  unfold auxiliaryEvaluation
  rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt Polynomial.natDegree_map_le
    (Nat.lt_succ_self P.natDegree))]
  refine (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_).trans_lt (by omega : D-1 < D)
  intro j _
  rw [Polynomial.coeff_map]
  exact Nat.le_sub_one_of_lt (auxiliaryTerm_degree_lt f Q z
    w wQ j D hf hQ hD (P.coeff j) (hP j))

theorem derivativeAux_weight (P : Source K) (m a w wQ k n0 d : ℕ)
    (hwa : w-2 ≤ a) (hdm : d ≤ m)
    (hweight : ∀ j e, e ∈ (P.coeff j).support →
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+wQ*j+
        reserve k n0 (e 1)*(a-(w-2)) < m*a)
    (hreserve : ∀ j e, e ∈ (P.coeff j).support → d ≤ e 1 → d ≤ reserve k n0 (e 1))
    (j : ℕ) (e : Fin 5 →₀ ℕ) (he : e ∈ (((derivativeAux^[d]) P).coeff j).support) :
    e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+wQ*j < (m-d)*a := by
  rw [iterate_derivativeAux_coeff] at he
  have hs := SecondJetGlobalDifferentiation.support_iterate (P.coeff j) d e he
  have hh := hweight j _ hs
  have hr := hreserve j _ hs (by
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    omega)
  simp [Finsupp.add_apply, Fin.ext_iff] at hh hr
  have hp := Nat.mul_le_mul_right (a-(w-2)) hr
  have ha : a-(w-2)+(w-2) = a := Nat.sub_add_cancel hwa
  have hm : (m-d)*a+d*a = m*a := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hdm]
  nlinarith

theorem le_rootMultiplicity_of_cleared (den p : Polynomial K) (q m : ℕ) (x : K)
    (hden : den.eval x ≠ 0) (hp : p ≠ 0)
    (hdvd : (Polynomial.X-Polynomial.C x)^m ∣ den^q*p) :
    m ≤ p.rootMultiplicity x := by
  have hq : (den^q).eval x ≠ 0 := by
    rw [Polynomial.eval_pow]
    exact pow_ne_zero _ hden
  have hqn : den^q ≠ 0 := by
    intro h
    exact hq (by rw [h, Polynomial.eval_zero])
  have hm := (Polynomial.le_rootMultiplicity_iff (mul_ne_zero hqn hp)).mpr hdvd
  rwa [Polynomial.rootMultiplicity_mul (mul_ne_zero hqn hp),
    Polynomial.rootMultiplicity_eq_zero hq, zero_add] at hm

theorem normalized_derivative_vanish
    (P : Source K) (A B : Poly (K := K)) (m a w wQ k n0 q d : ℕ)
    (ha : 0 < a) (hwa : w-2 ≤ a) (hdm : d < m)
    (hdegree : P.natDegree ≤ q)
    (hA : MvPolynomial.pderiv 1 A = 0) (hB : MvPolynomial.pderiv 1 B = 0)
    (hweight : ∀ j e, e ∈ (P.coeff j).support →
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+wQ*j+
        reserve k n0 (e 1)*(a-(w-2)) < m*a)
    (hreserve : ∀ j e, e ∈ (P.coeff j).support → d ≤ e 1 → d ≤ reserve k n0 (e 1))
    (nodes : N ↪ K) (u0 u1 : N → K)
    (f Q : Polynomial K) (hf : f.natDegree ≤ w) (hQ : Q.natDegree ≤ wQ)
    (z : K) (S : Finset N) (hS : a ≤ S.card)
    (hagree : ∀ i ∈ S, f.eval (nodes i) = u0 i + u1 i*z)
    (hden : ∀ i ∈ S, (specialize f z A).eval (nodes i) ≠ 0)
    (hequation : specialize f z B = specialize f z A * Q)
    (hcontact : ∀ i ∈ S, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) (clearAux A B q P))) :
    specialize f z ((MvPolynomial.pderiv 1)^[d] (clearAux A B q P)) = 0 := by
  classical
  let P' := (derivativeAux^[d]) P
  let R := auxiliaryEvaluation f Q z P'
  have hclear : specialize f z ((MvPolynomial.pderiv 1)^[d] (clearAux A B q P)) =
      (specialize f z A)^q * R := by
    rw [iterate_pderiv_clearAux A B q d P hA hB]
    exact specialize_clearAux A B q P' f Q z
      ((iterate_derivativeAux_natDegree_le P d).trans hdegree) hequation
  suffices hz : R = 0 by rw [hclear, hz, mul_zero]
  by_contra hR
  have hmult : ∀ i ∈ S, m-d ≤ R.rootMultiplicity (nodes i) := by
    intro i hi
    apply le_rootMultiplicity_of_cleared (specialize f z A) R q (m-d) (nodes i)
      (hden i hi) hR
    rw [← hclear]
    apply root_contact _ f (nodes i) (u0 i) (u1 i) z (m-d) (hagree i hi)
    apply SecondJetGlobalDifferentiation.local_derivative_contact
    simpa only [Nat.sub_add_cancel hdm.le] using hcontact i hi
  have hsum := BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
    R nodes S (m-d) hmult
  have hbound : R.natDegree < (m-d)*a := auxiliaryEvaluation_degree_lt
    f Q z P' w wQ ((m-d)*a) hf hQ (Nat.mul_pos (Nat.sub_pos_of_lt hdm) ha)
    (derivativeAux_weight P m a w wQ k n0 d hwa hdm.le hweight hreserve)
  exact (not_lt_of_ge ((Nat.mul_le_mul_left (m-d) hS).trans hsum)) hbound

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
