import ProximityPrize.SubmissionLower.Y3
namespace ProximityPrize.SubmissionLower.RCN217
open RCN077 RCN313
 RCN347 RCN055
noncomputable section
variable {K:Type*} [CommRing K]
private abbrev factorIdeal (F:Poly4 K):Ideal (Poly4 K):=Ideal.span {F}
private theorem baseDerivation_self (F:Poly4 K):baseDerivation F F=0:=by
 rw [baseDerivation_apply]
 unfold polyG polyH
 ring
private theorem baseDerivation_stable_factor (F:Poly4 K):
   ∀ P∈factorIdeal F,baseDerivation F P∈factorIdeal F:=by
 intro P hP
 rw [Ideal.mem_span_singleton] at hP ⊢
 obtain ⟨A,rfl⟩:=hP
 refine ⟨baseDerivation F A,?_⟩
 rw [leibniz_product,baseDerivation_self]
 ring
private def factorDerivation (F:Poly4 K):
   Derivation K (Poly4 K ⧸ factorIdeal F) (Poly4 K ⧸ factorIdeal F):=
 quotientDerivation (baseDerivation F) (factorIdeal F)
   (baseDerivation_stable_factor F)
private theorem factorDerivation_mk (F P:Poly4 K):
   factorDerivation F (Ideal.Quotient.mk (factorIdeal F) P)=
     Ideal.Quotient.mk (factorIdeal F) (baseDerivation F P):=
 quotientDerivation_mk _ _ _ P
private theorem factor_zero (F:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) F=0:=
 Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F)
private theorem polyH_mul_factor_mod (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (polyH K (F*Q))=
     Ideal.Quotient.mk (factorIdeal F) Q*
       Ideal.Quotient.mk (factorIdeal F) (polyH K F):=by
 unfold polyH
 rw [MvPolynomial.pderiv_mul]
 simp only [map_add,map_mul,factor_zero]
 ring
private theorem polyG_mul_factor_mod (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (polyG K (F*Q))=
     Ideal.Quotient.mk (factorIdeal F) Q*
       Ideal.Quotient.mk (factorIdeal F) (polyG K F):=by
 unfold polyG
 simp only [MvPolynomial.pderiv_mul,map_neg,map_add,map_mul,factor_zero]
 ring
private theorem baseDerivation_mul_factor_mod (F Q P:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (baseDerivation (F*Q) P)=
     Ideal.Quotient.mk (factorIdeal F) Q*
       factorDerivation F (Ideal.Quotient.mk (factorIdeal F) P):=by
 rw [factorDerivation_mk,baseDerivation_apply,baseDerivation_apply]
 simp only [map_add,map_mul]
 rw [polyH_mul_factor_mod,polyG_mul_factor_mod]
 ring
private theorem scaled_step_identity {A:Type*} [CommRing A] [Algebra K A]
   (D:Derivation K A A) (q h n nS:A) (b:ℕ)
   (hN:nS=q^(2*b)*n):
   q*h*(q*D nS)-(2*b:A)*nS*(q*D (q*h))=
     q^(2*(b+1))*(h*D n-(2*b:A)*n*D h):=by
 cases b with
 | zero =>
     simp only [hN,mul_zero,pow_zero,one_mul,Nat.cast_zero,
       zero_mul,sub_zero]
     ring
 | succ c =>
     rw [hN]
     simp only [leibniz_product,Derivation.leibniz_pow,nsmul_eq_mul,smul_eq_mul,
       Nat.cast_mul,Nat.cast_ofNat]
     have he:2*(c+1)=2*c+2:=by omega
     have hesub:2*c+2-1=2*c+1:=by omega
     have henext:2*(c+1+1)=2*c+4:=by omega
     rw [he,hesub,henext]
     have hp1:q^(2*c+1)=q^(2*c)*q:=by
       rw [pow_add,pow_one]
     have hp2:q^(2*c+2)=q^(2*c)*q^2:=by rw [pow_add]
     have hp4:q^(2*c+4)=q^(2*c)*q^4:=by rw [pow_add]
     rw [hp1,hp2,hp4]
     ring
private theorem numerator_scaling_mod (F Q:Poly4 K) (b:ℕ):
   Ideal.Quotient.mk (factorIdeal F) (numerator K (F*Q) b)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*b)*
       Ideal.Quotient.mk (factorIdeal F) (numerator K F b):=by
 induction b with
 | zero => simp
 | succ b ih =>
   change Ideal.Quotient.mk (factorIdeal F)
       (numeratorStep K (F*Q) b (numerator K (F*Q) b))=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*(b+1))*
       Ideal.Quotient.mk (factorIdeal F)
         (numeratorStep K F b (numerator K F b))
   rw [numeratorStep_eq,numeratorStep_eq]
   simp only [map_sub,map_mul,map_natCast]
   rw [polyH_mul_factor_mod,
     baseDerivation_mul_factor_mod F Q (numerator K (F*Q) b),
     baseDerivation_mul_factor_mod F Q (polyH K (F*Q))]
   rw [←factorDerivation_mk F (numerator K F b),
     ←factorDerivation_mk F (polyH K F)]
   have hDH:=congrArg (factorDerivation F) (polyH_mul_factor_mod F Q)
   rw [hDH]
   simp only [Nat.cast_mul,Nat.cast_ofNat]
   apply scaled_step_identity (factorDerivation F)
     (Ideal.Quotient.mk (factorIdeal F) Q)
     (Ideal.Quotient.mk (factorIdeal F) (polyH K F))
     (Ideal.Quotient.mk (factorIdeal F) (numerator K F b))
     (Ideal.Quotient.mk (factorIdeal F) (numerator K (F*Q) b))
     b
   exact ih
theorem numerator_sub_factor_power_mem (F Q:Poly4 K) (b:ℕ):
   numerator K (F*Q) b-Q^(2*b)*numerator K F b∈
     Ideal.span ({F}:Set (Poly4 K)):=by
 rw [←Ideal.Quotient.mk_eq_mk_iff_sub_mem]
 simpa only [map_mul,map_pow] using numerator_scaling_mod F Q b
theorem factor_dvd_numerator_sub_power (F Q:Poly4 K) (b:ℕ):
   F∣numerator K (F*Q) b-Q^(2*b)*numerator K F b:=by
 exact Ideal.mem_span_singleton.mp (numerator_sub_factor_power_mem F Q b)
theorem factor_dvd_numerator_sub_power_of_eq (F Q S:Poly4 K)
   (hS:S=F*Q) (b:ℕ):
   F∣numerator K S b-Q^(2*b)*numerator K F b:=by
 subst S
 exact factor_dvd_numerator_sub_power F Q b
end
end ProximityPrize.SubmissionLower.RCN217
