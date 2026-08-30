import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.C
import ProximityPrize.SubmissionLower.W
namespace ProximityPrize.SubmissionLower.ContactSharpYRecurrence
open ContactInterpolation ContactFactorCaps ContactTaylorNumerators
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
theorem polyH_Y_degree_pred_of_mem_box
   (F:Poly4 K) (D w L s c:ℕ) (hw:0 < w)
   (hD:D ≤ w*c+(w-1))
   (hbox:F∈globalCoefficientBox K D w L s):
   (polyH K F).degreeOf (1:Fin 4) ≤ c-1:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hs:=support_before_pderiv (2:Fin 4) F d hd
 have hc:=(hbox hs).2.2
 let e:Fin 4 →₀ ℕ:=d+Finsupp.single (2:Fin 4) 1
 have he:e=d+Finsupp.single (2:Fin 4) 1:=rfl
 change e∈F.support at hs
 change e 0+w*e 1+(w-1)*e 2 < D at hc
 have h0:e (0:Fin 4)=d 0:=by simp [he]
 have h1:e (1:Fin 4)=d 1:=by simp [he]
 have h2:e (2:Fin 4)=d 2+1:=by simp [he]
 rw [h0,h1,h2] at hc
 have hcontact:w*d 1+(w-1) < D:=by
   have hr:(w-1)*1 ≤ (w-1)*(d 2+1):=
     Nat.mul_le_mul_left (w-1) (by omega)
   calc
     w*d 1+(w-1) ≤
         d 0+w*d 1+(w-1)*(d 2+1):=by omega
     _ < D:=hc
 have hadd:w*d 1+(w-1) < w*c+(w-1):=
   hcontact.trans_le hD
 have hmul:w*d 1 < w*c:=Nat.add_lt_add_iff_right.mp hadd
 have hlt:d 1 < c:=(Nat.mul_lt_mul_left hw).mp hmul
 omega
theorem numeratorStep_Y_degree_bound
   (F M:Poly4 K) (b a c:ℕ) (hc:1 ≤ c)
   (hF:F.degreeOf (1:Fin 4) ≤ c)
   (hH:(polyH K F).degreeOf (1:Fin 4) ≤ c-1)
   (hM:M.degreeOf (1:Fin 4) ≤ a):
   (numeratorStep K F b M).degreeOf (1:Fin 4) ≤ a+(2*c-1):=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 change H.degreeOf (1:Fin 4) ≤ c-1 at hH
 have hR:R.degreeOf (1:Fin 4) ≤ 0:=by
   simp [R,MvPolynomial.degreeOf_X_of_ne
     (by decide:(1:Fin 4)≠(2:Fin 4))]
 have hG:G.degreeOf (1:Fin 4) ≤ c:=by
   simpa only [Nat.add_zero] using
     polyG_degree_bound (1:Fin 4) F c 0 hF hR
 have hH2:=degree_pow_bound (1:Fin 4) 2 hH
 have hMX:=pderiv_degree_bound (0:Fin 4) (1:Fin 4) M a hM
 have hMY:=pderiv_same_degree_bound (1:Fin 4) M a hM
 have hMR:=pderiv_degree_bound (2:Fin 4) (1:Fin 4) M a hM
 have hHX:=pderiv_degree_bound (0:Fin 4) (1:Fin 4) H (c-1) hH
 have hHY:=pderiv_same_degree_bound (1:Fin 4) H (c-1) hH
 have hHR:=pderiv_degree_bound (2:Fin 4) (1:Fin 4) H (c-1) hH
 have h1:(H^2*MvPolynomial.pderiv (0:Fin 4) M).degreeOf (1:Fin 4) ≤
     a+(2*c-1):=by
   have hh:=degree_mul_bound (1:Fin 4) hH2 hMX
   omega
 have h2:(R*H^2*MvPolynomial.pderiv (1:Fin 4) M).degreeOf (1:Fin 4) ≤
     a+(2*c-1):=by
   have hh:=degree_mul_bound (1:Fin 4)
     (degree_mul_bound (1:Fin 4) hR hH2) hMY
   omega
 have h3:(G*H*MvPolynomial.pderiv (2:Fin 4) M).degreeOf (1:Fin 4) ≤
     a+(2*c-1):=by
   have hh:=degree_mul_bound (1:Fin 4)
     (degree_mul_bound (1:Fin 4) hG hH) hMR
   omega
 have hbx:(H*MvPolynomial.pderiv (0:Fin 4) H).degreeOf (1:Fin 4) ≤
     2*c-1:=by
   have hh:=degree_mul_bound (1:Fin 4) hH hHX
   omega
 have hby:(R*H*MvPolynomial.pderiv (1:Fin 4) H).degreeOf (1:Fin 4) ≤
     2*c-1:=by
   have hh:=degree_mul_bound (1:Fin 4)
     (degree_mul_bound (1:Fin 4) hR hH) hHY
   omega
 have hbr:(G*MvPolynomial.pderiv (2:Fin 4) H).degreeOf (1:Fin 4) ≤
     2*c-1:=by
   have hh:=degree_mul_bound (1:Fin 4) hG hHR
   omega
 have hbrace:=degree_add_bound (1:Fin 4)
   (degree_add_bound (1:Fin 4) hbx hby) hbr
 have hn:(((2*b:ℕ):Poly4 K)).degreeOf (1:Fin 4) ≤ 0:=
   le_of_eq (degree_natCast_eq_zero (1:Fin 4) (2*b))
 have hnM:(((2*b:ℕ):Poly4 K)*M).degreeOf (1:Fin 4) ≤ a:=by
   simpa only [Nat.zero_add] using degree_mul_bound (1:Fin 4) hn hM
 have h4:=degree_mul_bound (1:Fin 4) hnM hbrace
 change (H^2*MvPolynomial.pderiv (0:Fin 4) M+
     R*H^2*MvPolynomial.pderiv (1:Fin 4) M+
     G*H*MvPolynomial.pderiv (2:Fin 4) M-
     ((2*b:ℕ):Poly4 K)*M*
       (H*MvPolynomial.pderiv (0:Fin 4) H+
         R*H*MvPolynomial.pderiv (1:Fin 4) H+
         G*MvPolynomial.pderiv (2:Fin 4) H)).degreeOf (1:Fin 4) ≤
       a+(2*c-1)
 exact degree_sub_bound (1:Fin 4)
   (degree_add_bound (1:Fin 4) (degree_add_bound (1:Fin 4) h1 h2) h3) h4
theorem numerator_Y_degree_bound
   (F:Poly4 K) (c:ℕ) (hc:1 ≤ c)
   (hF:F.degreeOf (1:Fin 4) ≤ c)
   (hH:(polyH K F).degreeOf (1:Fin 4) ≤ c-1)
   (b:ℕ):
   (numerator K F b).degreeOf (1:Fin 4) ≤ 1+b*(2*c-1):=by
 induction b with
 | zero => simp [numerator_zero]
 | succ b ih =>
     rw [numerator_succ]
     have hh:=numeratorStep_Y_degree_bound F (numerator K F b) b
       (1+b*(2*c-1)) c hc hF hH ih
     simpa only [Nat.add_mul,Nat.one_mul,add_assoc] using hh
theorem commonNumeratorTerm_Y_degree_bound
   (F:Poly4 K) (c:ℕ) (hc:1 ≤ c)
   (hF:F.degreeOf (1:Fin 4) ≤ c)
   (hH:(polyH K F).degreeOf (1:Fin 4) ≤ c-1)
   (w j:ℕ) (hj:j ≤ w) (coeffs:ℕ → K) (x:K):
   (commonNumeratorTerm F w coeffs x j).degreeOf (1:Fin 4) ≤
     1+w*(2*c-1):=by
 have hM:=numerator_Y_degree_bound F c hc hF hH j
 have hCM:(MvPolynomial.C (coeffs j)*numerator K F j).degreeOf (1:Fin 4) ≤
     1+j*(2*c-1):=
   (MvPolynomial.degreeOf_C_mul_le (numerator K F j) (1:Fin 4) (coeffs j)).trans hM
 have hHP:=degree_pow_bound (1:Fin 4) (2*(w-j)) hH
 have hXP:MvPolynomial.degreeOf (1:Fin 4)
     ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j) ≤ 0:=by
   simpa only [Nat.mul_zero] using degree_pow_bound (1:Fin 4) j
     (shiftedX_degree_bound (1:Fin 4) (by decide) x)
 have hterm:=degree_mul_bound (1:Fin 4)
   (degree_mul_bound (1:Fin 4) hCM hHP) hXP
 have hwj:j+(w-j)=w:=by omega
 have hcap:(1+j*(2*c-1))+2*(w-j)*(c-1)+0 ≤
     1+w*(2*c-1):=by
   have hdelta:2*c-1=2*(c-1)+1:=by omega
   rw [hdelta]
   calc
     (1+j*(2*(c-1)+1))+2*(w-j)*(c-1)+0=
         1+2*(j+(w-j))*(c-1)+j:=by ring
     _=1+2*w*(c-1)+j:=by rw [hwj]
     _ ≤ 1+2*w*(c-1)+w:=Nat.add_le_add_left hj _
     _=1+w*(2*(c-1)+1):=by ring
 simpa only [commonNumeratorTerm] using hterm.trans hcap
theorem clearedTaylorNumerator_Y_degree_bound
   (F:Poly4 K) (c:ℕ) (hc:1 ≤ c)
   (hF:F.degreeOf (1:Fin 4) ≤ c)
   (hH:(polyH K F).degreeOf (1:Fin 4) ≤ c-1)
   (w:ℕ) (coeffs:ℕ → K) (x:K):
   (clearedTaylorNumerator F w coeffs x).degreeOf (1:Fin 4) ≤
     1+w*(2*c-1):=by
 unfold clearedTaylorNumerator
 apply degree_sum_bound (1:Fin 4)
 intro j hj
 exact commonNumeratorTerm_Y_degree_bound F c hc hF hH w j
   (by have:=Finset.mem_range.mp hj;omega) coeffs x
theorem agreementNumerator_Y_degree_bound
   (F:Poly4 K) (c:ℕ) (hc:1 ≤ c)
   (hF:F.degreeOf (1:Fin 4) ≤ c)
   (hH:(polyH K F).degreeOf (1:Fin 4) ≤ c-1)
   (w:ℕ) (coeffs:ℕ → K) (x u₀ u₁:K):
   (agreementNumerator F w coeffs x u₀ u₁).degreeOf (1:Fin 4) ≤
     1+w*(2*c-1):=by
 unfold agreementNumerator
 apply degree_sub_bound (1:Fin 4)
 · exact clearedTaylorNumerator_Y_degree_bound F c hc hF hH w coeffs x
 · have ha:=affineSeedPolynomial_degree_bound (1:Fin 4) 0
     (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 4)≠3)]) u₀ u₁
   have hp:=degree_pow_bound (1:Fin 4) (2*w) hH
   have hm:=degree_mul_bound (1:Fin 4) ha hp
   have hdelta:2*c-1=2*(c-1)+1:=by omega
   apply hm.trans
   rw [hdelta]
   calc
     0+2*w*(c-1) ≤ 1+2*w*(c-1)+w:=by omega
     _=1+w*(2*(c-1)+1):=by ring
theorem sharp_Y_bounds_of_mem_box
   (F:Poly4 K) (D w L s c:ℕ) (hw:0 < w) (hc:1 ≤ c)
   (hD:D ≤ w*c+(w-1))
   (hbox:F∈globalCoefficientBox K D w L s)
   (b t:ℕ) (coeffs:ℕ → K) (x u₀ u₁:K):
   (numerator K F b).degreeOf (1:Fin 4) ≤ 1+b*(2*c-1)∧
     (agreementNumerator F t coeffs x u₀ u₁).degreeOf (1:Fin 4) ≤
       1+t*(2*c-1):=by
 have hY:=degreeOf_Y_le_of_mem_box F D w L s hw hbox
 have hcapped:F.degreeOf (1:Fin 4) ≤ c:=by
   apply hY.trans
   apply Nat.le_of_lt_succ
   apply (Nat.div_lt_iff_lt_mul hw).mpr
   have hwsub:w-1 < w:=Nat.sub_lt hw (by norm_num)
   calc
     D-1 ≤ D:=Nat.sub_le D 1
     _ ≤ w*c+(w-1):=hD
     _ < w*c+w:=Nat.add_lt_add_left hwsub _
     _=(c+1)*w:=by ring
 have hH:=polyH_Y_degree_pred_of_mem_box F D w L s c hw hD hbox
 exact ⟨numerator_Y_degree_bound F c hc hcapped hH b,
   agreementNumerator_Y_degree_bound F c hc hcapped hH t coeffs x u₀ u₁⟩
end
end ProximityPrize.SubmissionLower.ContactSharpYRecurrence
