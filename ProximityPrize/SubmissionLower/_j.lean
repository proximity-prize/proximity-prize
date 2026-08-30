import ProximityPrize.SubmissionLower.W
namespace ProximityPrize.SubmissionLower.ContactBaseIdealAlgebra6676Research
open ContactDifferentialRing ContactTaylorNumerators DifferentialTaylorCoefficients
noncomputable section
section Algebra
variable {K:Type*} [CommRing K]
def horizontalDerivation:Derivation K (Poly4 K) (Poly4 K):=
 MvPolynomial.pderiv (0:Fin 4)+
   (MvPolynomial.X (2:Fin 4):Poly4 K) • MvPolynomial.pderiv (1:Fin 4)
def baseDerivation (F:Poly4 K):Derivation K (Poly4 K) (Poly4 K):=
 polyH K F • horizontalDerivation+polyG K F • MvPolynomial.pderiv (2:Fin 4)
theorem baseDerivation_apply (F P:Poly4 K):
   baseDerivation F P=polyH K F*
     (MvPolynomial.pderiv (0:Fin 4) P+
       MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) P)+
     polyG K F*MvPolynomial.pderiv (2:Fin 4) P:=by
 simp only [baseDerivation,horizontalDerivation,Derivation.add_apply,
   Derivation.smul_apply,smul_eq_mul]
def baseIdeal (F:Poly4 K):Ideal (Poly4 K):=
 Ideal.span {polyH K F,polyG K F}
theorem H_mem_baseIdeal (F:Poly4 K):polyH K F∈baseIdeal F:=
 Ideal.subset_span (by simp)
theorem G_mem_baseIdeal (F:Poly4 K):polyG K F∈baseIdeal F:=
 Ideal.subset_span (by simp)
theorem baseDerivation_mem (F P:Poly4 K):baseDerivation F P∈baseIdeal F:=by
 rw [baseDerivation_apply]
 exact (baseIdeal F).add_mem
   ((baseIdeal F).mul_mem_right _ (H_mem_baseIdeal F))
   ((baseIdeal F).mul_mem_right _ (G_mem_baseIdeal F))
theorem derivation_preserves_ideal_pow {A:Type*} [CommRing A] [Algebra K A]
   (D:Derivation K A A) (I:Ideal A)
   (hI:∀ P∈I,D P∈I) (n:ℕ):∀ P∈I^n,D P∈I^n:=by
 induction n with
 | zero => simp
 | succ n ih =>
   rw [pow_succ]
   intro P hP
   refine Submodule.mul_induction_on hP ?_ ?_
   · intro P hP Q hQ
     rw [leibniz_product]
     exact (I^n*I).add_mem
       (Ideal.mul_mem_mul (ih P hP) hQ) (Ideal.mul_mem_mul hP (hI Q hQ))
   · intro P Q hP hQ
     simpa only [map_add] using (I^n*I).add_mem hP hQ
theorem baseDerivation_preserves_pow (F:Poly4 K) (n:ℕ)
   (P:Poly4 K) (hP:P∈baseIdeal F^n):
   baseDerivation F P∈baseIdeal F^n:=
 derivation_preserves_ideal_pow (baseDerivation F) (baseIdeal F)
   (fun P _ => baseDerivation_mem F P) n P hP
theorem numeratorStep_eq (F P:Poly4 K) (b:ℕ):
   numeratorStep K F b P=polyH K F*baseDerivation F P-
     (2*b:ℕ)*P*baseDerivation F (polyH K F):=by
 simp only [numeratorStep,clearedStep,baseDerivation_apply]
 ring
theorem numerator_one (F:Poly4 K):
   numerator K F 1=MvPolynomial.X (2:Fin 4)*polyH K F^2:=by
 simp [numerator,numeratorStep,clearedStep,MvPolynomial.pderiv_X]
theorem baseDerivation_R (F:Poly4 K):
   baseDerivation F (MvPolynomial.X (2:Fin 4))=polyG K F:=by
 simp [baseDerivation_apply,MvPolynomial.pderiv_X]
theorem numerator_two (F:Poly4 K):
   numerator K F 2=polyH K F^3*polyG K F:=by
 rw [numerator_succ,numerator_one,numeratorStep_eq,leibniz_product,
   baseDerivation_R,Derivation.leibniz_pow]
 simp only [smul_eq_mul,nsmul_eq_mul,Nat.reduceSub,Nat.cast_ofNat]
 ring
def baseNumerator (F:Poly4 K):ℕ → Poly4 K
 | 0 => polyG K F
 | n+1 => polyH K F*baseDerivation F (baseNumerator F n)-
     (2*n+1:ℕ)*baseNumerator F n*baseDerivation F (polyH K F)
theorem numeratorStep_H_cube (F P:Poly4 K) (n:ℕ):
   numeratorStep K F (n+2) (polyH K F^3*P)=
     polyH K F^3*(polyH K F*baseDerivation F P-
       (2*n+1:ℕ)*P*baseDerivation F (polyH K F)):=by
 rw [numeratorStep_eq,leibniz_product,Derivation.leibniz_pow]
 simp only [smul_eq_mul,nsmul_eq_mul,Nat.reduceSub,Nat.cast_add,
   Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
 ring
theorem numerator_eq_H_cube (F:Poly4 K) (n:ℕ):
   numerator K F (n+2)=polyH K F^3*baseNumerator F n:=by
 induction n with
 | zero => exact numerator_two F
 | succ n ih =>
   rw [show n+1+2=(n+2)+1 by omega,numerator_succ,ih,
     numeratorStep_H_cube]
   rfl
theorem baseNumerator_mem_pow (F:Poly4 K) (n:ℕ):
   baseNumerator F n∈baseIdeal F^(n+1):=by
 induction n with
 | zero => simpa only [baseNumerator,Nat.zero_add,pow_one] using G_mem_baseIdeal F
 | succ n ih =>
   rw [baseNumerator,pow_succ]
   apply (baseIdeal F^(n+1)*baseIdeal F).sub_mem
   · simpa only [mul_comm (baseDerivation F (baseNumerator F n))] using
       Ideal.mul_mem_mul (baseDerivation_preserves_pow F (n+1) _ ih)
         (H_mem_baseIdeal F)
   · simpa only [mul_assoc] using
       (baseIdeal F^(n+1)*baseIdeal F).mul_mem_left (2*n+1:ℕ)
         (Ideal.mul_mem_mul ih (baseDerivation_mem F (polyH K F)))
theorem numerator_mem_pow (F:Poly4 K) (b:ℕ) (hb:2 ≤ b):
   numerator K F b∈baseIdeal F^(b+2):=by
 obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le hb
 rw [Nat.add_comm 2 n,numerator_eq_H_cube]
 have h:=Ideal.mul_mem_mul (Ideal.pow_mem_pow (H_mem_baseIdeal F) 3)
   (baseNumerator_mem_pow F n)
 rw [←pow_add] at h
 simpa only [show 3+(n+1)=n+2+2 by omega] using h
end Algebra
section Agreement
variable {K:Type*} [Field K]
theorem commonNumeratorTerm_mem_pow (F:Poly4 K) (d j:ℕ)
   (hd:2 ≤ d) (hj:j ≤ d) (c:ℕ → K) (x:K):
   commonNumeratorTerm F d c x j∈baseIdeal F^(d+2):=by
 unfold commonNumeratorTerm
 apply (baseIdeal F^(d+2)).mul_mem_right
 by_cases hj2:2 ≤ j
 · have h:=Ideal.mul_mem_mul (numerator_mem_pow F j hj2)
     (Ideal.pow_mem_pow (H_mem_baseIdeal F) (2*(d-j)))
   rw [←pow_add] at h
   have h':numerator K F j*polyH K F^(2*(d-j))∈
       baseIdeal F^(d+2):=Ideal.pow_le_pow_right (by omega) h
   simpa only [mul_assoc] using (baseIdeal F^(d+2)).mul_mem_left
     (MvPolynomial.C (c j)) h'
 · have hj01:j=0∨j=1:=by omega
   rcases hj01 with rfl | rfl
   · exact (baseIdeal F^(d+2)).mul_mem_left _
       (Ideal.pow_le_pow_right (by omega)
         (Ideal.pow_mem_pow (H_mem_baseIdeal F) (2*(d-0))))
   · rw [numerator_one]
     have hpow:2+2*(d-1)=2*d:=by omega
     have hmem:polyH K F^(2*d)∈baseIdeal F^(d+2):=
       Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow (H_mem_baseIdeal F) _)
     convert (baseIdeal F^(d+2)).mul_mem_left
       (MvPolynomial.C (c 1)*MvPolynomial.X (2:Fin 4)) hmem using 1
     rw [←hpow,pow_add]
     ring
theorem agreementNumerator_mem_pow (F:Poly4 K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   agreementNumerator F d c x u₀ u₁∈baseIdeal F^(d+2):=by
 unfold agreementNumerator clearedTaylorNumerator
 apply (baseIdeal F^(d+2)).sub_mem
 · exact (baseIdeal F^(d+2)).sum_mem fun j hj =>
     commonNumeratorTerm_mem_pow F d j hd (by simpa using Finset.mem_range.mp hj) c x
 · exact (baseIdeal F^(d+2)).mul_mem_left _
     (Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow (H_mem_baseIdeal F) (2*d)))
end Agreement
end
end ProximityPrize.SubmissionLower.ContactBaseIdealAlgebra6676Research
