import ProximityPrize.SubmissionLower.C
set_option Elab.async false
set_option autoImplicit true
section
namespace WI
noncomputable section
open aR dN rW MvPolynomial
open scoped BigOperators
private theorem cGC (J:n8) (hd:dimension J≤2) :by
    classical
    exact (∀ P (hp:J.IsMinimalPrime P),oA J P hp.isPrime ≠ ⊤) ∧
      ∑ P∈J.minimalPrimesFinset,
        (Yg J P:ℚ)*(affineHilbertPolynomial P).coeff 2 ≤
        (affineHilbertPolynomial J).coeff 2 := by
  classical
  let T:=J.minimalPrimesFinset
  suffices aux : ∀ I:n8,J≤I →
      (∀ P (hp:J.IsMinimalPrime P),oA I P hp.isPrime ≠ ⊤) ∧
      ∑ P∈T,(Yg I P:ℚ)*(affineHilbertPolynomial P).coeff 2 ≤
        (affineHilbertPolynomial I).coeff 2 from aux J le_rfl
  intro I
  induction I using WellFounded.induction (wellFounded_gt (α:=n8)) with
  | h I ih =>
    intro hJI
    by_cases hI:I = ⊤
    · subst I
      have hz (P:n8) (hp:P.IsPrime) :oA ⊤ P hp=0 :=
        aIs hp (by simpa using hp.ne_top)
      exact ⟨fun P hp=> by simp [hz P hp.isPrime],by
        refine le_of_eq ?_
        simp only [Yg,affineHilbertPolynomial_top,Polynomial.coeff_zero]
        apply Finset.sum_eq_zero
        intro P hP
        have hp:=(Ideal.mem_minimalPrimesFinset.mp hP).isPrime
        simp [dite_eq_left hp,hz P hp]⟩
    obtain ⟨g,hg,hprime⟩:=b2k I hI
    let A:n8:=I.colon {g}
    let B:n8:=I ⊔ Ideal.span {g}
    have hIA:I≤A:=Ideal.le_colon
    have hIB:I<B:=lt_of_le_not_ge le_sup_left
      (fun h=>hg (h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))))
    obtain ⟨hfin,hbudget⟩:=ih B hIB (hJI.trans hIB.le)
    have hstep (P:n8) (hp:J.IsMinimalPrime P) :
        oA I P hp.isPrime =
          oA A P hp.isPrime+oA B P hp.isPrime :=
      be6 I P hp.isPrime g
    have hterm (P:n8) (hp:J.IsMinimalPrime P) :
        oA A P hp.isPrime=if P=A then 1 else 0:= by
      split_ifs with h
      · subst P
        exact brM A hp.isPrime
      · exact aIs hp.isPrime
          (fun hAP=>h (le_antisymm (hp.2 ⟨hprime,hJI.trans hIA⟩ hAP) hAP))
    have hfinite (P:n8) (hp:J.IsMinimalPrime P) :
        oA A P hp.isPrime ≠ ⊤ := by rw [hterm P hp]; split_ifs <;> simp
    have hweight (P:n8) (hP:P∈T) :
        (Yg I P:ℚ)=(Yg B P:ℚ)+(if P=A then 1 else 0) := by
      have hp:=Ideal.mem_minimalPrimesFinset.mp hP
      simp only [Yg,dite_eq_left hp.isPrime]
      rw [hstep P hp,ENat.toNat_add (hfinite P hp) (hfin P hp),hterm P hp,Nat.cast_add]
      split_ifs <;> simp [add_comm]
    have hdim:=(natDegree_affineHilbertPolynomial_le_of_le hJI).trans hd
    refine ⟨fun P hp=> by
      rw [hstep P hp]
      exact WithTop.add_ne_top.mpr ⟨hfinite P hp,hfin P hp⟩,?_⟩
    calc
      _=(∑ P∈T,(Yg B P:ℚ)*(affineHilbertPolynomial P).coeff 2) +
          (if A∈T then (affineHilbertPolynomial A).coeff 2 else 0) := by
        rw [← Finset.sum_ite_eq' T A (fun P=>(affineHilbertPolynomial P).coeff 2),
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [hweight P hP,add_mul,ite_mul,one_mul,zero_mul]
      _≤(affineHilbertPolynomial B).coeff 2+(affineHilbertPolynomial A).coeff 2 := by
        apply add_le_add hbudget
        split_ifs
        · exact le_rfl
        · exact cGp A ((natDegree_affineHilbertPolynomial_le_of_le hIA).trans hdim)
      _≤_:=cUM I g hdim
end
end WI
end
