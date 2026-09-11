import ProximityPrize.SubmissionLower.Part.F005_02
section Compact_PackedLegacyCore2
section PackedLegacy_Z2
namespace ProximityPrize.SubmissionLower.RCN121
open RCN095

theorem z_flag_trapezoid_budget
   (p q:FlagDegree) (m:ℕ) (hm:m ≤ q.all):
   m*(p.yz+p.all)+p.all*(q.yz+q.all)-m*p.all ≤
     flagMixed p q unitZFlag:=by
 calc
   m*(p.yz+p.all)+p.all*(q.yz+q.all)-m*p.all ≤
       q.all*(p.yz+p.all)+p.all*(q.yz+q.all)-
         q.all*p.all:=
     trapezoid_budget_mono p.all q.all (p.yz+p.all)
       (q.yz+q.all) m (by omega) hm
   _=flagMixed p q unitZFlag:=by
     have hsum:
         q.all*(p.yz+p.all)+p.all*(q.yz+q.all)=
           q.all*p.all+flagMixed p q unitZFlag:=by
       simp [flagMixed,unitZFlag]
       ring
     rw [hsum,Nat.add_sub_cancel_left]
end ProximityPrize.SubmissionLower.RCN121
end PackedLegacy_Z2

/-! Packed from ProximityPrize.SubmissionLower.I. -/
section PackedLegacy_I
namespace ProximityPrize.SubmissionLower.RCN237
open scoped Classical BigOperators
open RCN264 RCN095 RCN121 RCN165 RCN156 RCN213 RCN215 RCN275
noncomputable section
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
structure PrimeFlagBudgetFamily (p q:FlagDegree) where
 zCost:RegularComponent Omega G T H → ℕ
 yzCost:RegularComponent Omega G T H → ℕ
 allCost:RegularComponent Omega G T H → ℕ
 primeBudget:∀ C:RegularComponent Omega G T H,
   PrimeFlagZeroBudget C.1 (fun r↦
     r.zOnly*zCost C+r.yz*yzCost C+r.all*allCost C)
 sum_zCost_le:(∑ C:RegularComponent Omega G T H,zCost C) ≤
   flagMixed p q unitZFlag
 sum_yzCost_le:(∑ C:RegularComponent Omega G T H,yzCost C) ≤
   flagMixed p q unitYZFlag
 sum_allCost_le:(∑ C:RegularComponent Omega G T H,allCost C) ≤
   flagMixed p q unitAllFlag
def PrimeFlagBudgetFamily.weightedCost
   {p q:FlagDegree} (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
   (r:FlagDegree) (C:RegularComponent Omega G T H):ℕ:=
 r.zOnly*B.zCost C+r.yz*B.yzCost C+r.all*B.allCost C
theorem PrimeFlagBudgetFamily.sum_weightedCost_le
   {p q:FlagDegree} (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
   (r:FlagDegree):
   (∑ C:RegularComponent Omega G T H,B.weightedCost r C) ≤
     flagMixed p q r:=by
 calc
   (∑ C:RegularComponent Omega G T H,B.weightedCost r C)=
       r.zOnly*(∑ C:RegularComponent Omega G T H,B.zCost C)+
       r.yz*(∑ C:RegularComponent Omega G T H,B.yzCost C)+
       r.all*(∑ C:RegularComponent Omega G T H,B.allCost C):=by
     simp only [PrimeFlagBudgetFamily.weightedCost,
       Finset.sum_add_distrib,Finset.mul_sum]
   _ ≤ r.zOnly*flagMixed p q unitZFlag+
       r.yz*flagMixed p q unitYZFlag+
       r.all*flagMixed p q unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add
         (Nat.mul_le_mul_left r.zOnly B.sum_zCost_le)
         (Nat.mul_le_mul_left r.yz B.sum_yzCost_le))
       (Nat.mul_le_mul_left r.all B.sum_allCost_le)
   _=flagMixed p q r:=(flagMixed_projection_decomposition p q r).symm
end
end ProximityPrize.SubmissionLower.RCN237
end PackedLegacy_I

/-! Packed from ProximityPrize.SubmissionLower.B1. -/
section PackedLegacy_B1
namespace ProximityPrize.SubmissionLower.RCN066
open scoped Classical BigOperators
open RCN072 RCN264 RCN095 RCN272 RCN165 RCN237
noncomputable section
variable {K:Type} [Field K]
abbrev Poly3:=MvPolynomial (Fin 3) K
theorem mem_iff_of_sub_mem (P:Ideal (Poly3 (K:=K)))
   {A B:Poly3 (K:=K)} (h:A - B ∈ P):A ∈ P ↔ B ∈ P:=by
 constructor
 · intro hA
   simpa only [sub_sub_cancel] using P.sub_mem hA h
 · intro hB
   simpa only [sub_add_cancel] using P.add_mem h hB
theorem sub_mem_of_dvd (P:Ideal (Poly3 (K:=K)))
   {G A B:Poly3 (K:=K)} (hG:G ∈ P) (h:G ∣ A - B) :
   A - B ∈ P:=by
 obtain ⟨Q,hQ⟩:=h
 rw [hQ]
 exact P.mul_mem_right Q hG
theorem cutIdeal_eq_of_dvd_sub {G T T':Poly3 (K:=K)}
   (h:G ∣ T - T'):cutIdeal K G T = cutIdeal K G T':=by
 have hG:G ∈ cutIdeal K G T:=Ideal.subset_span (by simp)
 have hG':G ∈ cutIdeal K G T':=Ideal.subset_span (by simp)
 have hT:T ∈ cutIdeal K G T:=Ideal.subset_span (by simp)
 have hT':T' ∈ cutIdeal K G T':=Ideal.subset_span (by simp)
 have hd:=sub_mem_of_dvd (cutIdeal K G T) hG h
 have hd':=sub_mem_of_dvd (cutIdeal K G T') hG' h
 apply le_antisymm
 · apply Ideal.span_le.mpr
   intro A hA
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
   rcases hA with rfl | rfl
   · exact hG'
   · exact (mem_iff_of_sub_mem _ hd').mpr hT'
 · apply Ideal.span_le.mpr
   intro A hA
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
   rcases hA with rfl | rfl
   · exact hG
   · exact (mem_iff_of_sub_mem _ hd).mp hT
theorem regularComponents_eq_of_dvd_sub {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T - T') :
   regularComponents K G T H = regularComponents K G T' H:=by
 classical
 ext P
 simp only [regularComponents,Finset.mem_filter,mem_componentFamily,
   cutIdeal_eq_of_dvd_sub h]
set_option maxHeartbeats 2000000 in
def regularComponentEquiv {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T - T') :
   RegularComponent K G T H ≃ RegularComponent K G T' H where
 toFun C:=⟨C.1,(regularComponents_eq_of_dvd_sub h) ▸ C.2⟩
 invFun C:=⟨C.1,(regularComponents_eq_of_dvd_sub h).symm ▸ C.2⟩
 left_inv C:=by rfl
 right_inv C:=by rfl
@[simp] theorem regularComponentEquiv_val {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T - T') (C:RegularComponent K G T H) :
   (regularComponentEquiv h C).1 = C.1:=rfl
@[simp] theorem regularComponentEquiv_symm_val {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T - T') (C:RegularComponent K G T' H) :
   ((regularComponentEquiv h).symm C).1 = C.1:=rfl
theorem eval_eq_of_sub_mem (P:Ideal (Poly3 (K:=K)))
   {A B:Poly3 (K:=K)} (h:A - B ∈ P) (v:Fin 3 → K)
   (hv:P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) :
   MvPolynomial.aeval v A = MvPolynomial.aeval v B:=by
 have hz:=hv h
 change MvPolynomial.aeval v (A - B) = 0 at hz
 rw [map_sub] at hz
 exact sub_eq_zero.mp hz
theorem finiteZeroSetBound_of_sub_mem (P:Ideal (Poly3 (K:=K)))
   {A B:Poly3 (K:=K)} {cost:ℕ}
   (h:A - B ∈ P) (hB:FiniteZeroSetBound P B cost) :
   FiniteZeroSetBound P A cost:=by
 intro points hpointsP hpointsA
 apply hB points hpointsP
 intro v hv
 rw [← eval_eq_of_sub_mem P h v (hpointsP v hv)]
 exact hpointsA v hv
def PolynomialInFlagMod (P:Ideal (Poly3 (K:=K)))
   (r:FlagDegree) (A:Poly3 (K:=K)):Prop :=
 ∃ B,PolynomialInFlag r B ∧ A - B ∈ P
theorem PolynomialInFlagMod.mono {P Q:Ideal (Poly3 (K:=K))}
   {r:FlagDegree} {A:Poly3 (K:=K)} (hPQ:P ≤ Q)
   (h:PolynomialInFlagMod P r A):PolynomialInFlagMod Q r A:=by
 obtain ⟨B,hB,hAB⟩:=h
 exact ⟨B,hB,hPQ hAB⟩
theorem PrimeFlagZeroBudget.zero_le_congr
   {P:Ideal (Poly3 (K:=K))} {cost:FlagDegree → ℕ}
   (B:PrimeFlagZeroBudget P cost) (r:FlagDegree)
   (A:Poly3 (K:=K)) (hA:PolynomialInFlagMod P r A)
   (hproper:A ∉ P):FiniteZeroSetBound P A (cost r):=by
 obtain ⟨A',hflag,hcongr⟩:=hA
 have hproper':A' ∉ P:=by
   intro hmem
   exact hproper ((mem_iff_of_sub_mem P hcongr).mpr hmem)
 exact finiteZeroSetBound_of_sub_mem P hcongr (B.zero_le r A' hflag hproper')
def PrimeFlagBudgetFamily.ofCongruentCut
   {G T T' H:Poly3 (K:=K)} {p q:FlagDegree}
   (h:G ∣ T - T')
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T') (H:=H) p q) :
   PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q where
 zCost C:=B.zCost (regularComponentEquiv h C)
 yzCost C:=B.yzCost (regularComponentEquiv h C)
 allCost C:=B.allCost (regularComponentEquiv h C)
 primeBudget C:=B.primeBudget (regularComponentEquiv h C)
 sum_zCost_le:=by
   simpa only [(regularComponentEquiv h).sum_comp B.zCost] using B.sum_zCost_le
 sum_yzCost_le:=by
   simpa only [(regularComponentEquiv h).sum_comp B.yzCost] using B.sum_yzCost_le
 sum_allCost_le:=by
   simpa only [(regularComponentEquiv h).sum_comp B.allCost] using B.sum_allCost_le
end
end ProximityPrize.SubmissionLower.RCN066
end PackedLegacy_B1

/-! Packed from ProximityPrize.SubmissionLower.E5. -/
section PackedLegacy_E5
namespace ProximityPrize.SubmissionLower.RCN263
open RCN136 RCN231 RCN313 RCN238 RCN156 RCN234 RCN095 RCN275 RCN262 RCN066
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
def reducedAgreementDirection (P:ResidualSupportParameters):FlagDegree :=
 ⟨2 * (P.total - P.ys),2 * (P.ys - P.s),2 * P.s - 2⟩
def reducedResidualAgreementFlag
   (P:ResidualSupportParameters) (d:ℕ):FlagDegree :=
 ⟨(reducedAgreementDirection P).zOnly * d,
   1 + (reducedAgreementDirection P).yz * d,
   (reducedAgreementDirection P).all * d⟩
theorem reducedResidualAgreementFlag_ys
   (P:ResidualSupportParameters) (d:ℕ) :
   (reducedResidualAgreementFlag P d).yz +
       (reducedResidualAgreementFlag P d).all =
     1 + d * (2 * P.ys - 2):=by
 have hs:=P.s_le_ys
 have h1:=P.one_le_s
 have hcoeff :
     2 * (P.ys - P.s) + (2 * P.s - 2) = 2 * P.ys - 2:=by
   rw [Nat.mul_sub_left_distrib]
   omega
 simp only [reducedResidualAgreementFlag,reducedAgreementDirection]
 rw [← hcoeff]
 ring
theorem reducedResidualAgreementFlag_total
   (P:ResidualSupportParameters) (d:ℕ) :
   (reducedResidualAgreementFlag P d).zOnly +
       (reducedResidualAgreementFlag P d).yz +
       (reducedResidualAgreementFlag P d).all =
     1 + d * (2 * P.total - 2):=by
 have hs:=P.s_le_ys
 have ht:=P.ys_le_total
 have h1:=P.one_le_s
 have hcoeff:2 * (P.total - P.ys) + 2 * (P.ys - P.s) +
     (2 * P.s - 2) = 2 * P.total - 2:=by
   rw [Nat.mul_sub_left_distrib,Nat.mul_sub_left_distrib]
   omega
 simp only [reducedResidualAgreementFlag,reducedAgreementDirection]
 rw [← hcoeff]
 ring
def reducedAgreementPolynomial (phi:Polynomial K →+* Omega)
   (P:ResidualSupportParameters) (F:MvPolynomial (Fin 4) K)
   (d:ℕ) (x u0 u1:K):MvPolynomial (Fin 3) Omega :=
 surfaceMap phi (reducedAgreementNumerator F P.s d
   (fun j ↦ (j.factorial:K)⁻¹) x u0 u1)
theorem surfaceMap_reducedAgreement_in_flag
   (phi:Polynomial K →+* Omega) (P:ResidualSupportParameters)
   {F:MvPolynomial (Fin 4) K} (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K) :
   PolynomialInFlag (reducedResidualAgreementFlag P d)
     (surfaceMap phi
       (reducedAgreementNumerator F P.s d coeffs x u0 u1)):=by
 have hR:=reducedAgreementNumerator_R_degree_bound F P.s P.one_le_s
   H.coordinate_bounds.2.1 d coeffs x u0 u1
 have hYS:=reducedAgreementNumerator_wt_le residualYSWeights rfl rfl rfl
   F P.s P.ys P.one_le_s P.two_le_ys H.ys_weight d coeffs x u0 u1
 have hTotal:=reducedAgreementNumerator_wt_le residualTotalWeights rfl rfl rfl
   F P.s P.total P.one_le_s (P.two_le_ys.trans P.ys_le_total)
   H.total_weight d coeffs x u0 u1
 rw [show residualYSWeights 3 = 0 from rfl] at hYS
 rw [show residualTotalWeights 3 = 1 from rfl] at hTotal
 norm_num at hYS hTotal
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (support_surfaceMap_subset phi
     (reducedAgreementNumerator F P.s d coeffs x u0 u1) he)
 have hqR:=(MvPolynomial.monomial_le_degreeOf (2:Fin 4) hq).trans hR
 have hqYS :=
   (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS
 have hqTotal :=
   (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTotal
 rw [RCN081.weight_fin4] at hqYS hqTotal
 change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 0 ≤ _ at hqYS
 change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 1 ≤ _ at hqTotal
 norm_num at hqYS hqTotal
 change q 2 ≤ (reducedResidualAgreementFlag P d).all ∧
   q 1 + q 2 ≤ (reducedResidualAgreementFlag P d).yz +
     (reducedResidualAgreementFlag P d).all ∧
   q 1 + q 2 + q 3 ≤ (reducedResidualAgreementFlag P d).zOnly +
     (reducedResidualAgreementFlag P d).yz +
     (reducedResidualAgreementFlag P d).all
 refine ⟨?_,?_,?_⟩
 · change q 2 ≤ (2 * P.s - 2) * d
   have hs:2 * (P.s - 1) = 2 * P.s - 2:=by omega
   have heq:2 * d * (P.s - 1) = (2 * P.s - 2) * d:=by
     rw [← hs]
     ring
   rw [heq] at hqR
   exact hqR
 · rw [reducedResidualAgreementFlag_ys]
   have hs:2 * (P.ys - 1) = 2 * P.ys - 2:=by omega
   have heq:2 * d * (P.ys - 1) = d * (2 * P.ys - 2):=by
     rw [← hs]
     ring
   rw [heq] at hqYS
   exact hqYS
 · rw [reducedResidualAgreementFlag_total]
   have hs:2 * (P.total - 1) = 2 * P.total - 2:=by
     have:=P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)
     omega
   have heq:2 * d * (P.total - 1) = d * (2 * P.total - 2):=by
     rw [← hs]
     ring
   rw [heq] at hqTotal
   exact hqTotal
end
end ProximityPrize.SubmissionLower.RCN263
end PackedLegacy_E5

/-! Packed from ProximityPrize.SubmissionLower.Y3. -/
section PackedLegacy_Y3
namespace ProximityPrize.SubmissionLower.RCN055
open RCN077 RCN313 RCN347
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
end Algebra
section Agreement
variable {K:Type*} [Field K]
end Agreement
end
end ProximityPrize.SubmissionLower.RCN055
end PackedLegacy_Y3

/-! Packed from ProximityPrize.SubmissionLower.A6. -/
section PackedLegacy_A6
namespace ProximityPrize.SubmissionLower.RCN056
open RCN077 RCN313 RCN347 RCN055
noncomputable section
variable {K:Type*} [CommRing K]
def sameContribution (F:Poly4 K) (n j:ℕ) (P:Poly4 K):Poly4 K:=
 polyH K F*horizontalDerivation P-
   (n+j:ℕ)*P*horizontalDerivation (polyH K F)+
     (j:ℕ)*P*MvPolynomial.pderiv (2:Fin 4) (polyG K F)
def downContribution (F:Poly4 K) (j:ℕ) (P:Poly4 K):Poly4 K:=
 (j:ℕ)*P*horizontalDerivation (polyG K F)
def upContribution (F:Poly4 K) (n j:ℕ) (P:Poly4 K):Poly4 K:=
 polyH K F*MvPolynomial.pderiv (2:Fin 4) P-
   (n+j:ℕ)*P*MvPolynomial.pderiv (2:Fin 4) (polyH K F)
def baseMonomial (F:Poly4 K) (k j:ℕ) (P:Poly4 K):Poly4 K:=
 polyH K F^(k-j)*polyG K F^j*P
def baseStep (F:Poly4 K) (n:ℕ) (P:Poly4 K):Poly4 K:=
 polyH K F*baseDerivation F P-
   (2*n+1:ℕ)*P*baseDerivation F (polyH K F)
theorem baseStep_monomial (F P:Poly4 K) (n j:ℕ) (hj:j ≤ n+1):
   baseStep F n (baseMonomial F (n+1) j P)=
     baseMonomial F (n+2) j (sameContribution F n j P)+
     baseMonomial F (n+2) (j-1) (downContribution F j P)+
     baseMonomial F (n+2) (j+1) (upContribution F n j P):=by
 cases j with
 | zero =>
   have he:n+2-1=n+1:=by omega
   simp only [baseStep,baseMonomial,sameContribution,downContribution,
     upContribution,baseDerivation,Derivation.add_apply,Derivation.smul_apply,
     smul_eq_mul,Nat.sub_zero,Nat.zero_sub,Nat.cast_zero,zero_mul,mul_zero,
     pow_zero,mul_one,Nat.zero_add,he,add_zero,leibniz_product,
     Derivation.leibniz_pow,nsmul_eq_mul,Nat.add_sub_cancel]
   simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ]
   ring
 | succ j =>
   by_cases ht:j=n
   · subst j
     simp only [baseStep,baseMonomial,sameContribution,downContribution,
       upContribution,baseDerivation,Derivation.add_apply,Derivation.smul_apply,
       smul_eq_mul,Nat.add_sub_add_left,Nat.add_sub_cancel,Nat.sub_self,
       Nat.reduceSub,Nat.add_sub_cancel_left,pow_zero,one_mul,
       leibniz_product,Derivation.leibniz_pow,nsmul_eq_mul]
     simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ]
     ring
   · have hjn:j+1 ≤ n:=by omega
     obtain ⟨u,hu⟩:=Nat.exists_eq_add_of_le hjn
     subst n
     have e₁:j+1+u+1-(j+1)=u+1:=by omega
     have e₂:j+1+u+2-(j+1)=u+2:=by omega
     have e₃:j+1+u+2-j=u+3:=by omega
     have e₄:j+1+u+2-(j+1+1)=u+1:=by omega
     simp only [baseStep,baseMonomial,sameContribution,downContribution,
       upContribution,baseDerivation,Derivation.add_apply,Derivation.smul_apply,
       smul_eq_mul,Nat.add_sub_cancel,e₁,e₂,e₃,e₄,
       leibniz_product,Derivation.leibniz_pow,nsmul_eq_mul]
     simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ]
     ring
def coefficientStep (F:Poly4 K) (n:ℕ) (C:ℕ → Poly4 K) (j:ℕ):Poly4 K:=
 sameContribution F n j (C j)+downContribution F (j+1) (C (j+1))+
   if j=0 then 0 else upContribution F n (j-1) (C (j-1))
def baseCoefficients (F:Poly4 K):ℕ → ℕ → Poly4 K
 | 0,j => if j=1 then 1 else 0
 | n+1,j => coefficientStep F n (baseCoefficients F n) j
theorem baseCoefficients_zero (F:Poly4 K) (n j:ℕ) (hj:n+1 < j):
   baseCoefficients F n j=0:=by
 induction n generalizing j with
 | zero => simp [baseCoefficients,show j≠1 by omega]
 | succ n ih =>
   simp [baseCoefficients,coefficientStep,ih j (by omega),
     ih (j+1) (by omega),ih (j-1) (by omega),
     sameContribution,downContribution,upContribution]
theorem baseStep_sum (F:Poly4 K) (n:ℕ) (s:Finset ℕ) (P:ℕ → Poly4 K):
   baseStep F n (∑ j∈s,P j)=∑ j∈s,baseStep F n (P j):=by
 simp only [baseStep,map_sum,Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib]
theorem coefficientStep_represents (F:Poly4 K) (n:ℕ) (C:ℕ → Poly4 K)
   (hC:∀ j,n+1 < j → C j=0):
   baseStep F n (∑ j∈Finset.range (n+2),baseMonomial F (n+1) j (C j))=
     ∑ j∈Finset.range (n+3),baseMonomial F (n+2) j (coefficientStep F n C j):=by
 let a j:=baseMonomial F (n+2) j (sameContribution F n j (C j))
 let b j:=baseMonomial F (n+2) (j-1) (downContribution F j (C j))
 let c j:=baseMonomial F (n+2) (j+1) (upContribution F n j (C j))
 have ha:(∑ j∈Finset.range (n+2),a j)=∑ j∈Finset.range (n+3),a j:=by
   conv_rhs => rw [Finset.sum_range_succ]
   simp [a,hC (n+2) (by omega),sameContribution,baseMonomial]
 have hb0:b 0=0:=by simp [b,downContribution,baseMonomial]
 have hb2:b (n+2)=0:=by
   simp [b,hC (n+2) (by omega),downContribution,baseMonomial]
 have hb3:b (n+3)=0:=by
   simp [b,hC (n+3) (by omega),downContribution,baseMonomial]
 have hb:(∑ j∈Finset.range (n+2),b j)=
     ∑ j∈Finset.range (n+3),b (j+1):=by
   calc
     _=∑ j∈Finset.range (n+1),b (j+1):=by
       rw [Finset.sum_range_succ']
       simp only [hb0,add_zero]
     _=_:=by
       symm
       rw [Finset.sum_range_succ,Finset.sum_range_succ]
       simp only [show n+1+1=n+2 by omega,show n+2+1=n+3 by omega,
         hb2,hb3,add_zero]
 have hc:(∑ j∈Finset.range (n+2),c j)=
     ∑ j∈Finset.range (n+3),baseMonomial F (n+2) j
       (if j=0 then 0 else upContribution F n (j-1) (C (j-1))):=by
   conv_rhs => rw [Finset.sum_range_succ']
   simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,
     Nat.add_sub_cancel,baseMonomial,mul_zero,add_zero]
   rfl
 rw [baseStep_sum]
 calc
   _=∑ j∈Finset.range (n+2),(a j+b j+c j):=by
     apply Finset.sum_congr rfl
     intro j hj
     exact baseStep_monomial F (C j) n j (by have:=Finset.mem_range.mp hj;omega)
   _=(∑ j∈Finset.range (n+2),a j)+
       (∑ j∈Finset.range (n+2),b j)+(∑ j∈Finset.range (n+2),c j):=by
     simp only [Finset.sum_add_distrib]
   _=_:=by
     rw [ha,hb,hc]
     simp only [a,b,coefficientStep,baseMonomial,mul_add,
       Finset.sum_add_distrib,Nat.add_sub_cancel]
theorem baseNumerator_eq_sum (F:Poly4 K) (n:ℕ):
   baseNumerator F n=
     ∑ j∈Finset.range (n+2),baseMonomial F (n+1) j (baseCoefficients F n j):=by
 induction n with
 | zero => simp [baseNumerator,baseCoefficients,baseMonomial]
 | succ n ih =>
   change baseStep F n (baseNumerator F n)=_
   rw [ih,coefficientStep_represents F n _ (baseCoefficients_zero F n)]
   rfl
theorem numerator_eq_coefficient_sum (F:Poly4 K) (n:ℕ):
   numerator K F (n+2)=polyH K F^3*
     ∑ j∈Finset.range (n+2),
       polyH K F^(n+1-j)*polyG K F^j*baseCoefficients F n j:=by
 rw [numerator_eq_H_cube,baseNumerator_eq_sum]
 rfl
end
end ProximityPrize.SubmissionLower.RCN056
end PackedLegacy_A6

/-! Packed from ProximityPrize.SubmissionLower.DX. -/
section PackedLegacy_DX
namespace ProximityPrize.SubmissionLower.RCN053
open RCN077 RCN313 RCN055 RCN056
noncomputable section
variable {K:Type*} [Field K]
def agreementLow (c:ℕ → K) (x u₀ u₁:K):Poly4 K:=
 MvPolynomial.C (c 0)*MvPolynomial.X (1:Fin 4)+
   MvPolynomial.C (c 1)*MvPolynomial.X (2:Fin 4)*
     (MvPolynomial.C x-MvPolynomial.X (0:Fin 4))-affineSeedPolynomial u₀ u₁
def agreementHighCoefficient (F:Poly4 K) (d:ℕ) (c:ℕ → K) (x:K)
   (n j:ℕ):Poly4 K:=
 MvPolynomial.C (c (n+2))*polyH K F^(d-(n+2)+3)*
   baseCoefficients F n j*(MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^(n+2)
def agreementCoefficients (F:Poly4 K) (d:ℕ) (c:ℕ → K) (x u₀ u₁:K)
   (j:ℕ):Poly4 K:=
 (if j=0 then polyH K F^(d+1)*agreementLow c x u₀ u₁ else 0)+
   ∑ n∈Finset.range (d-1),agreementHighCoefficient F d c x n j
theorem agreementNumerator_eq_low_add_sum (F:Poly4 K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   agreementNumerator F d c x u₀ u₁=polyH K F^(2*d)*agreementLow c x u₀ u₁+
     ∑ n∈Finset.range (d-1),commonNumeratorTerm F d c x (n+2):=by
 have hpow:polyH K F^2*polyH K F^(2*(d-1))=polyH K F^(2*d):=by
   rw [←pow_add,show 2+2*(d-1)=2*d by omega]
 unfold agreementNumerator clearedTaylorNumerator
 rw [show d+1=2+(d-1) by omega,Finset.sum_range_add]
 simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add,
   show ∀ n:ℕ,2+n=n+2 from fun n => Nat.add_comm 2 n]
 simp only [commonNumeratorTerm,numerator_one,numerator_zero,Nat.sub_zero,
   pow_zero,mul_one,pow_one]
 unfold agreementLow
 linear_combination (MvPolynomial.C (c 1)*MvPolynomial.X (2:Fin 4)*
   (MvPolynomial.C x-MvPolynomial.X (0:Fin 4)))*hpow
theorem highCoefficient_monomial (F:Poly4 K) (d n j:ℕ)
   (hn:n+2 ≤ d) (hj:j ≤ n+1) (c:ℕ → K) (x:K):
   baseMonomial F (d-1) j (agreementHighCoefficient F d c x n j)=
     MvPolynomial.C (c (n+2))*polyH K F^3*
       (polyH K F^(n+1-j)*polyG K F^j*baseCoefficients F n j)*
         polyH K F^(2*(d-(n+2)))*
           (MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^(n+2):=by
 have hp:polyH K F^(d-1-j)*polyH K F^(d-(n+2)+3)=
     polyH K F^3*polyH K F^(n+1-j)*polyH K F^(2*(d-(n+2))):=by
   simp only [←pow_add]
   congr 1
   omega
 unfold baseMonomial agreementHighCoefficient
 linear_combination (MvPolynomial.C (c (n+2))*polyG K F^j*
   baseCoefficients F n j*(MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^(n+2))*hp
theorem commonNumeratorTerm_eq_coefficient_sum (F:Poly4 K) (d n:ℕ)
   (hn:n+2 ≤ d) (c:ℕ → K) (x:K):
   commonNumeratorTerm F d c x (n+2)=
     ∑ j∈Finset.range d,baseMonomial F (d-1) j
       (agreementHighCoefficient F d c x n j):=by
 have hs:(∑ j∈Finset.range (n+2),baseMonomial F (d-1) j
     (agreementHighCoefficient F d c x n j))=
     ∑ j∈Finset.range d,baseMonomial F (d-1) j
       (agreementHighCoefficient F d c x n j):=by
   apply Finset.sum_subset (Finset.range_mono hn)
   intro j _ hj
   have hz:=baseCoefficients_zero F n j (by simp only [Finset.mem_range] at hj;omega)
   simp only [baseMonomial,agreementHighCoefficient,hz,mul_zero,zero_mul]
 rw [←hs]
 unfold commonNumeratorTerm
 rw [numerator_eq_coefficient_sum]
 simp only [Finset.mul_sum,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro j hj
 simpa only [mul_assoc] using (highCoefficient_monomial F d n j hn
   (by have:=Finset.mem_range.mp hj;omega) c x).symm
theorem agreementNumerator_eq_coefficient_sum (F:Poly4 K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   agreementNumerator F d c x u₀ u₁=
     ∑ j∈Finset.range d,polyH K F^(d-1-j)*polyG K F^j*
       agreementCoefficients F d c x u₀ u₁ j:=by
 rw [agreementNumerator_eq_low_add_sum F d hd c x u₀ u₁]
 have hlo:(∑ j∈Finset.range d,polyH K F^(d-1-j)*polyG K F^j*
     (if j=0 then polyH K F^(d+1)*agreementLow c x u₀ u₁ else 0))=
     polyH K F^(2*d)*agreementLow c x u₀ u₁:=by
   rw [Finset.sum_eq_single 0]
   · simp only [Nat.sub_zero,pow_zero,mul_one,if_true]
     rw [←mul_assoc, ←pow_add,show d-1+(d+1)=2*d by omega]
   · intro j _ hj
     simp only [if_neg hj,mul_zero]
   · intro hj
     exact (hj (Finset.mem_range.mpr (by omega))).elim
 simp only [agreementCoefficients,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
 rw [hlo,Finset.sum_comm]
 apply congrArg (fun P:Poly4 K => polyH K F^(2*d)*agreementLow c x u₀ u₁+P)
 apply Finset.sum_congr rfl
 intro n hn
 exact commonNumeratorTerm_eq_coefficient_sum F d n
   (by have:=Finset.mem_range.mp hn;omega) c x
end
end ProximityPrize.SubmissionLower.RCN053
end PackedLegacy_DX

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.DZ. -/
section PackedLegacy_DZ
namespace ProximityPrize.SubmissionLower.RCN057
open RCN313 RCN055 RCN056 RCN234
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
private theorem pderiv_eq_zero_of_wt_lt (weights:Fin 4 → ℕ) (P:Poly K) (i:Fin 4)
   (hP:wt weights P < weights i):MvPolynomial.pderiv i P=0:=by
 apply MvPolynomial.support_eq_empty.mp
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro d hd
 have hh:=MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i P d hd)
 simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
 change Finsupp.weight weights d+weights i ≤ wt weights P at hh
 omega
def WeightBound (w:Fin 4 → ℕ) (P:Poly K) (c:ℤ):Prop:=
 P=0∨(wt w P:ℤ) ≤ c
namespace WeightBound
variable {w:Fin 4 → ℕ} {P Q:Poly K} {a b:ℤ}
theorem mono (h:WeightBound w P a) (hab:a ≤ b):WeightBound w P b:=
 h.imp_right (fun hp => hp.trans hab)
theorem add (hP:WeightBound w P a) (hQ:WeightBound w Q a):
   WeightBound w (P+Q) a:=by
 rcases hP with rfl | hp
 · simpa only [zero_add] using hQ
 rcases hQ with rfl | hq
 · rw [add_zero]
   exact Or.inr hp
 right
 have h:(wt w (P+Q):ℤ) ≤ max (wt w P:ℤ) (wt w Q:ℤ):=by
   exact_mod_cast wt_add_le w P Q
 exact h.trans (max_le hp hq)
theorem neg (hP:WeightBound w P a):WeightBound w (-P) a:=by
 rcases hP with rfl | hp
 · exact Or.inl neg_zero
 exact Or.inr (by simpa only [wt_neg] using hp)
theorem sub (hP:WeightBound w P a) (hQ:WeightBound w Q a):
   WeightBound w (P-Q) a:=by
 simpa only [sub_eq_add_neg] using hP.add hQ.neg
theorem mul (hP:WeightBound w P a) (hQ:WeightBound w Q b):
   WeightBound w (P*Q) (a+b):=by
 rcases hP with rfl | hp
 · exact Or.inl (zero_mul _)
 rcases hQ with rfl | hq
 · exact Or.inl (mul_zero _)
 right
 have h:(wt w (P*Q):ℤ) ≤ (wt w P:ℤ)+(wt w Q:ℤ):=by
   exact_mod_cast wt_mul_le w P Q
 linarith
theorem natCast (n:ℕ):WeightBound w (n:Poly K) 0:=
 Or.inr (by simp only [wt_natCast,Nat.cast_zero,le_refl])
theorem scale (n:ℕ) (hP:WeightBound w P a):WeightBound w ((n:Poly K)*P) a:=by
 simpa only [zero_add] using (natCast n).mul hP
theorem pderiv (hP:WeightBound w P a) (i:Fin 4):
   WeightBound w (MvPolynomial.pderiv i P) (a-w i):=by
 by_cases hz:MvPolynomial.pderiv i P=0
 · exact Or.inl hz
 rcases hP with rfl | hp
 · exact (hz (map_zero _)).elim
 right
 have hi:w i ≤ wt w P:=by
   by_contra hh
   exact hz (pderiv_eq_zero_of_wt_lt w P i (by omega))
 have hd:=wt_pderiv_le w P i (wt w P) le_rfl
 have hsum:wt w (MvPolynomial.pderiv i P)+w i ≤ wt w P:=by omega
 have hsum':(wt w (MvPolynomial.pderiv i P):ℤ)+w i ≤ wt w P:=by
   exact_mod_cast hsum
 linarith
theorem horizontal (hP:WeightBound w P a) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t ≤ 1):
   WeightBound w (horizontalDerivation P) (a+1-t):=by
 have hx:=hP.pderiv (0:Fin 4)
 have hy:=hP.pderiv (1:Fin 4)
 have hr:WeightBound w (MvPolynomial.X (2:Fin 4):Poly K) 1:=
   Or.inr (by simp only [wt_X,hR,Nat.cast_one,le_refl])
 simp only [hX,Nat.cast_zero,sub_zero] at hx
 rw [hY] at hy
 have hxy:WeightBound w (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) P)
     (a+1-t):=by convert hr.mul hy using 1;ring
 have ht':(t:ℤ) ≤ 1:=by exact_mod_cast ht
 simpa only [horizontalDerivation,Derivation.add_apply,Derivation.smul_apply,
   smul_eq_mul] using (hx.mono (by linarith)).add hxy
end WeightBound
theorem contribution_bounds (w:Fin 4 → ℕ) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t ≤ 1)
   (F P:Poly K) (C a:ℤ) (hF:WeightBound w F C) (hP:WeightBound w P a)
   (n j:ℕ):
   WeightBound w (sameContribution F n j P) (a+C-t)∧
   WeightBound w (downContribution F j P) (a+C+2-2*t)∧
   WeightBound w (upContribution F n j P) (a+C-2):=by
 have hH:WeightBound w (polyH K F) (C-1):=by
   simpa only [polyH,hR,Nat.cast_one] using hF.pderiv (2:Fin 4)
 have hG:WeightBound w (polyG K F) (C+1-t):=by
   simpa only [polyG,horizontalDerivation,Derivation.add_apply,
     Derivation.smul_apply,smul_eq_mul] using (hF.horizontal t hX hY hR ht).neg
 have hDH:=hH.horizontal t hX hY hR ht
 have hDG:=hG.horizontal t hX hY hR ht
 have hDP:=hP.horizontal t hX hY hR ht
 have hGR:=hG.pderiv (2:Fin 4)
 have hHR:=hH.pderiv (2:Fin 4)
 have hPR:=hP.pderiv (2:Fin 4)
 simp only [hR,Nat.cast_one] at hGR hHR hPR
 refine ⟨?_,?_,?_⟩
 · unfold sameContribution
   apply WeightBound.add
   · apply WeightBound.sub
     · convert hH.mul hDP using 1;ring
     · convert (hP.scale (n+j)).mul hDH using 1;ring
   · convert (hP.scale j).mul hGR using 1;ring
 · unfold downContribution
   convert (hP.scale j).mul hDG using 1;ring
 · unfold upContribution
   apply WeightBound.sub
   · convert hH.mul hPR using 1;ring
   · convert (hP.scale (n+j)).mul hHR using 1;ring
theorem baseCoefficients_weightBound (w:Fin 4 → ℕ) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t ≤ 1)
   (F:Poly K) (C:ℤ) (hF:WeightBound w F C) (n j:ℕ):
   WeightBound w (baseCoefficients F n j)
     (2-t+n*(C-t)-j*(2-t)):=by
 induction n generalizing j with
 | zero =>
   by_cases hj:j=1
   · subst j
     simp only [baseCoefficients,↓reduceIte]
     convert WeightBound.natCast (w:=w) (K:=K) 1 using 1 <;> push_cast <;> ring
   · exact Or.inl (by simp [baseCoefficients,hj])
 | succ n ih =>
   rw [baseCoefficients,coefficientStep]
   apply WeightBound.add
   · apply WeightBound.add
     · convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih j) n j).1 using 1
       push_cast
       ring
     · convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih (j+1)) n (j+1)).2.1
         using 1
       push_cast
       ring
   · by_cases hj:j=0
     · rw [if_pos hj]
       exact Or.inl rfl
     · rw [if_neg hj]
       have hj1:1 ≤ j:=by omega
       convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih (j-1)) n (j-1)).2.2
         using 1
       simp only [Nat.cast_sub hj1,Nat.cast_one,Nat.cast_add]
       ring
end
end ProximityPrize.SubmissionLower.RCN057
end PackedLegacy_DZ

/-! Packed from ProximityPrize.SubmissionLower.DY. -/
section PackedLegacy_DY
namespace ProximityPrize.SubmissionLower.RCN054
open RCN313 RCN055 RCN056 RCN057 RCN053 RCN234 RCN095
noncomputable section
variable {K:Type*} [Field K]
theorem weightBound_C (w:Fin 4 → ℕ) (c:K):
   WeightBound w (MvPolynomial.C c:Poly K) 0:=
 Or.inr (by simp only [wt_C,Nat.cast_zero,le_refl])
theorem weightBound_pow {w:Fin 4 → ℕ} {P:Poly K} {a:ℤ}
   (hP:WeightBound w P a) (n:ℕ):WeightBound w (P^n) (n*a):=by
 induction n with
 | zero => simpa only [pow_zero,Nat.cast_zero,zero_mul,Nat.cast_one] using
     (WeightBound.natCast (w:=w) (K:=K) 1)
 | succ n ih =>
   rw [pow_succ]
   convert ih.mul hP using 1
   push_cast
   ring
theorem weightBound_sum {w:Fin 4 → ℕ} {a:ℤ} (I:Finset ℕ) (P:ℕ → Poly K)
   (hP:∀ i∈I,WeightBound w (P i) a):WeightBound w (∑ i∈I,P i) a:=by
 classical
 induction I using Finset.induction_on with
 | empty => exact Or.inl (by simp)
 | @insert i I hi ih =>
   rw [Finset.sum_insert hi]
   exact (hP i (Finset.mem_insert_self _ _)).add
     (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))
theorem weightBound_shift (w:Fin 4 → ℕ) (hX:w 0=0) (x:K):
   WeightBound w (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly K) 0:=
 (weightBound_C w x).sub (Or.inr (by simp only [wt_X,hX,Nat.cast_zero,le_refl]))
theorem agreementLow_weightBound (w:Fin 4 → ℕ) (hX:w 0=0)
   (hY:w 1 ≤ 1) (hR:w 2=1) (hZ:w 3 ≤ 1)
   (c:ℕ → K) (x u₀ u₁:K):WeightBound w (agreementLow c x u₀ u₁) 1:=by
 have hvar (i:Fin 4) (hi:w i ≤ 1):
     WeightBound w (MvPolynomial.X i:Poly K) 1:=by
   right
   rw [wt_X]
   exact_mod_cast hi
 have h₀:=(weightBound_C w (c 0)).mul (hvar 1 hY)
 have h₁:=((weightBound_C w (c 1)).mul (hvar 2 (by omega))).mul (weightBound_shift w hX x)
 have hseed:=((weightBound_C w u₀).mono (by norm_num:(0:ℤ) ≤ 1)).add
   (by simpa only [add_zero] using (hvar 3 hZ).mul (weightBound_C w u₁))
 simpa only [agreementLow,affineSeedPolynomial,zero_add,add_zero] using (h₀.add h₁).sub hseed
theorem agreementCoefficients_weightBound (w:Fin 4 → ℕ) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (hZ:w 3 ≤ 1) (ht:t ≤ 1)
   (F:Poly K) (C:ℤ) (hF:WeightBound w F C) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K) (j:ℕ):
   WeightBound w (agreementCoefficients F d c x u₀ u₁ j)
     ((d+1:ℕ)*(C-1)+1+(d-1:ℕ)*(1-(t:ℤ))-j*(2-(t:ℤ))):=by
 have ht':(t:ℤ) ≤ 1:=by exact_mod_cast ht
 have hH:WeightBound w (polyH K F) (C-1):=by
   simpa only [polyH,hR,Nat.cast_one] using hF.pderiv (2:Fin 4)
 unfold agreementCoefficients
 apply WeightBound.add
 · by_cases hj:j=0
   · subst j
     rw [if_pos rfl]
     apply ((weightBound_pow hH (d+1)).mul
       (agreementLow_weightBound w hX (by omega) hR hZ c x u₀ u₁)).mono
     simp only [Nat.cast_zero,zero_mul,sub_zero]
     have hn:(0:ℤ) ≤ (d-1:ℕ):=Nat.cast_nonneg _
     nlinarith
   · rw [if_neg hj]
     exact Or.inl rfl
 · apply weightBound_sum
   intro n hn
   have hn':n+2 ≤ d:=by have:=Finset.mem_range.mp hn;omega
   have he:((d-(n+2)+3:ℕ):ℤ)=(d:ℤ)-n+1:=by
     push_cast [Nat.cast_sub hn']
     ring
   have hn'':(n:ℤ)+2 ≤ d:=by exact_mod_cast hn'
   have hd':((d-1:ℕ):ℤ)=(d:ℤ)-1:=by omega
   have hterm:=(((weightBound_C w (c (n+2))).mul
     (weightBound_pow hH (d-(n+2)+3))).mul
       (baseCoefficients_weightBound w t hX hY hR ht F C hF n j)).mul
         (weightBound_pow (weightBound_shift w hX x) (n+2))
   apply hterm.mono
   rw [he,hd']
   push_cast
   nlinarith
theorem agreementCoefficients_support_bounds (F:Poly K) (s M L:ℕ)
   (hR:F.degreeOf (2:Fin 4) ≤ s) (hYR:wt ![0,1,1,0] F ≤ M)
   (hAll:wt ![0,1,1,1] F ≤ L) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K) (j:ℕ):
   (agreementCoefficients F d c x u₀ u₁ j).degreeOf (2:Fin 4) ≤ (d+1)*s-1-2*j∧
   wt ![0,1,1,0] (agreementCoefficients F d c x u₀ u₁ j) ≤ (d+1)*M-d-j∧
   wt ![0,1,1,1] (agreementCoefficients F d c x u₀ u₁ j) ≤ (d+1)*L-d-j:=by
 have hcoord (P:Poly K):wt (Pi.single (2:Fin 4) 1) P=P.degreeOf (2:Fin 4):=by
   rw [wt,MvPolynomial.weightedTotalDegree,MvPolynomial.degreeOf_eq_sup]
   apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => P.support.sup f)
   funext e
   exact Finsupp.weight_single_one_apply _ e
 have hbound (w:Fin 4 → ℕ) (t:ℕ) (hX:w 0=0) (hY:w 1=t)
     (hR':w 2=1) (hZ:w 3 ≤ 1) (ht:t ≤ 1) (N:ℕ) (hF:wt w F ≤ N):=
   agreementCoefficients_weightBound w t hX hY hR' hZ ht F N
     (Or.inr (by exact_mod_cast hF)) d hd c x u₀ u₁ j
 constructor
 · have h:=hbound (Pi.single (2:Fin 4) 1) 0 (by simp) (by simp) (by simp)
     (by simp) (by omega) s (by simpa only [hcoord] using hR)
   rcases h with hz | hb
   · simp [hz]
   · rw [hcoord] at hb
     have he:((d-1:ℕ):ℤ)=(d:ℤ)-1:=by omega
     rw [he] at hb
     push_cast at hb
     have hh:((agreementCoefficients F d c x u₀ u₁ j).degreeOf (2:Fin 4):ℤ)+1+
         2*j ≤ (d+1:ℕ)*s:=by push_cast;nlinarith
     have hn:(agreementCoefficients F d c x u₀ u₁ j).degreeOf (2:Fin 4)+1+
         2*j ≤ (d+1)*s:=by exact_mod_cast hh
     omega
 · have cumulative (w:Fin 4 → ℕ) (hX:w 0=0) (hY:w 1=1)
       (hR':w 2=1) (hZ:w 3 ≤ 1) (N:ℕ) (hF:wt w F ≤ N):
       wt w (agreementCoefficients F d c x u₀ u₁ j) ≤ (d+1)*N-d-j:=by
     rcases hbound w 1 hX hY hR' hZ le_rfl N hF with hz | hb
     · simp [hz,wt,MvPolynomial.weightedTotalDegree]
     · have hh:(wt w (agreementCoefficients F d c x u₀ u₁ j):ℤ)+d+j ≤
           (d+1:ℕ)*N:=by push_cast at hb ⊢;nlinarith
       have hn:wt w (agreementCoefficients F d c x u₀ u₁ j)+d+j ≤
           (d+1)*N:=by exact_mod_cast hh
       omega
   exact ⟨cumulative _ rfl rfl rfl (by decide) M hYR,
     cumulative _ rfl rfl rfl (by decide) L hAll⟩
def coefficientFlag (a b s d j:ℕ):FlagDegree:=
 ⟨(d+1)*a,1+(d+1)*b-d+j,(d+1)*s-1-2*j⟩
def hFlag (a b s:ℕ):FlagDegree:=⟨a,b,s-1⟩
def gFlag (a b s:ℕ):FlagDegree:=⟨a,b-1,s+1⟩
def directionFlag (a b s:ℕ):FlagDegree:=⟨2*a,2*b-1,2*s-1⟩
theorem coefficientFlag_cumulative (a b s d j:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hj:j < d):
   (coefficientFlag a b s d j).all=(d+1)*s-1-2*j∧
   (coefficientFlag a b s d j).yz+(coefficientFlag a b s d j).all=
     (d+1)*(b+s)-d-j∧
   (coefficientFlag a b s d j).zOnly+(coefficientFlag a b s d j).yz+
     (coefficientFlag a b s d j).all=(d+1)*(a+b+s)-d-j:=by
 obtain ⟨b,rfl⟩:=Nat.exists_eq_add_of_le hb
 obtain ⟨s,rfl⟩:=Nat.exists_eq_add_of_le hs
 obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
 simp only [coefficientFlag,Nat.succ_eq_add_one,Nat.mul_add,Nat.add_mul,
   Nat.mul_one,Nat.one_mul]
 exact ⟨trivial,by omega,by omega⟩
theorem coefficientFlag_nonnegative_form (a b s d j:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hj:j < d):coefficientFlag a b s d j=
     ⟨(d+1)*a,(d+1)*(b-1)+2+j,
       (d+1)*(s-2)+3+2*(d-1-j)⟩:=by
 obtain ⟨b,rfl⟩:=Nat.exists_eq_add_of_le hb
 obtain ⟨s,rfl⟩:=Nat.exists_eq_add_of_le hs
 obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
 dsimp only [coefficientFlag]
 congr 1 <;> simp only [Nat.succ_eq_add_one,Nat.mul_add,Nat.add_mul,Nat.mul_one,
   Nat.one_mul,Nat.add_sub_cancel_left] <;> omega
theorem coefficientFlag_add_baseMonomial (a b s d j:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hj:j < d):
   coefficientFlag a b s d j+(d-1-j) • hFlag a b s+j • gFlag a b s=
     unitYZFlag+d • directionFlag a b s:=by
 rw [coefficientFlag_nonnegative_form a b s d j hb hs hj]
 obtain ⟨b,rfl⟩:=Nat.exists_eq_add_of_le hb
 obtain ⟨s,rfl⟩:=Nat.exists_eq_add_of_le hs
 obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
 have hk:j+1+k-1-j=k:=by omega
 have hs':2+s-1=1+s:=by omega
 have hb':2*(1+b)-1=1+2*b:=by omega
 have hs'':2*(2+s)-1=3+2*s:=by omega
 simp only [hk,hFlag,gFlag,directionFlag,unitYZFlag,Nat.add_sub_cancel_left,
   hs',hb',hs'']
 change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
 congr 1 <;> simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
   <;> dsimp <;> ring
theorem agreementCoefficients_in_flag (F:Poly K) (a b s:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hR:F.degreeOf (2:Fin 4) ≤ s) (hYR:wt ![0,1,1,0] F ≤ b+s)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K) (j:ℕ) (hj:j < d):
   ∀ e∈(agreementCoefficients F d c x u₀ u₁ j).support,
     e 2 ≤ (coefficientFlag a b s d j).all∧
     e 1+e 2 ≤ (coefficientFlag a b s d j).yz+(coefficientFlag a b s d j).all∧
     e 1+e 2+e 3 ≤ (coefficientFlag a b s d j).zOnly+
       (coefficientFlag a b s d j).yz+(coefficientFlag a b s d j).all:=by
 intro e he
 obtain ⟨hr,hyr,ht⟩:=agreementCoefficients_support_bounds F s (b+s) (a+b+s)
   hR hYR hAll d hd c x u₀ u₁ j
 obtain ⟨fr,fyr,ft⟩:=coefficientFlag_cumulative a b s d j hb hs hj
 rw [ft,fyr,fr]
 have heR:=(MvPolynomial.le_degreeOf_of_mem_support (2:Fin 4) he).trans hr
 have heYR:=(MvPolynomial.le_weightedTotalDegree ![0,1,1,0] he).trans hyr
 have heT:=(MvPolynomial.le_weightedTotalDegree ![0,1,1,1] he).trans ht
 rw [RCN081.weight_fin4] at heYR heT
 change e 0*0+e 1*1+e 2*1+e 3*0 ≤ _ at heYR
 change e 0*0+e 1*1+e 2*1+e 3*1 ≤ _ at heT
 simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero,Nat.zero_add] at heYR heT
 exact ⟨heR,heYR,heT⟩
theorem surfaceMap_agreementCoefficients_in_flag {Ω:Type*} [Field Ω]
   (φ:Polynomial K →+*Ω) (F:Poly K) (a b s:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hR:F.degreeOf (2:Fin 4) ≤ s) (hYR:wt ![0,1,1,0] F ≤ b+s)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K) (j:ℕ) (hj:j < d):
   PolynomialInFlag (coefficientFlag a b s d j)
     (RCN136.surfaceMap φ (agreementCoefficients F d c x u₀ u₁ j)):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (RCN136.support_surfaceMap_subset φ _ he)
 exact agreementCoefficients_in_flag F a b s hb hs hR hYR hAll d hd c x u₀ u₁ j hj q hq
theorem surfaceMap_agreementNumerator_eq_coefficient_sum {Ω:Type*} [Field Ω]
   (φ:Polynomial K →+*Ω) (F:Poly K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   RCN136.surfaceMap φ (agreementNumerator F d c x u₀ u₁)=
     ∑ j∈Finset.range d,RCN136.surfaceMap φ (polyH K F)^(d-1-j)*
       RCN136.surfaceMap φ (polyG K F)^j*
         RCN136.surfaceMap φ (agreementCoefficients F d c x u₀ u₁ j):=by
 rw [agreementNumerator_eq_coefficient_sum F d hd c x u₀ u₁]
 simp only [map_sum,map_mul,map_pow]
end
end ProximityPrize.SubmissionLower.RCN054
end PackedLegacy_DY

/-! Packed from ProximityPrize.SubmissionLower.D2. -/
section PackedLegacy_D2
namespace ProximityPrize.SubmissionLower.RCN207
open scoped Classical BigOperators Pointwise
open RCN095
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
variable {K:Type*} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K
def filteredCut {R:Type*} [CommRing R] (k:ℕ) (B:Fin (k+1) → R)
   (H G:R):R:=∑ j,B j*H^(k-j.val)*G^j.val
def movingEquation (H G Q U:Poly) (t:K):Poly:=
 H*(MvPolynomial.C t-Q)-U*G
def eliminatedCut (k:ℕ) (B:Fin (k+1) → Poly) (Q U:Poly) (t:K):Poly:=
 filteredCut k B U (MvPolynomial.C t-Q)
theorem map_filteredCut {R S:Type*} [CommRing R] [CommRing S]
   (ev:R →+*S) (k:ℕ) (B:Fin (k+1) → R) (H G:R):
   ev (filteredCut k B H G)=filteredCut k (fun j↦ev (B j)) (ev H) (ev G):=by
 simp [filteredCut]
theorem binary_clearing {R:Type*} [CommRing R] (k:ℕ) (B:Fin (k+1) → R)
   (H G U V:R) (hrel:H*V=U*G):
   H^k*filteredCut k B U V=U^k*filteredCut k B H G:=by
 unfold filteredCut
 rw [Finset.mul_sum,Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro j _
 have hj:k-j.val+j.val=k:=Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)
 have hh:H^k=H^(k-j.val)*H^j.val:=by rw [←pow_add,hj]
 have hu:U^k=U^(k-j.val)*U^j.val:=by rw [←pow_add,hj]
 calc
   _=B j*H^(k-j.val)*U^(k-j.val)*(H*V)^j.val:=by
     rw [hh,mul_pow];ring
   _=B j*H^(k-j.val)*U^(k-j.val)*(U*G)^j.val:=by rw [hrel]
   _=_:=by rw [hu,mul_pow];ring
theorem clearing_at_equation {R:Type*} [CommRing R] (ev:Poly →+*R)
   (k:ℕ) (B:Fin (k+1) → Poly) (H G Q U:Poly) (t:K)
   (hN:ev (movingEquation H G Q U t)=0):
   ev H^k*ev (eliminatedCut k B Q U t)=
     ev U^k*ev (filteredCut k B H G):=by
 have hrel:ev H*ev (MvPolynomial.C t-Q)=ev U*ev G:=by
   simpa [movingEquation,sub_eq_zero] using hN
 simp only [eliminatedCut,map_filteredCut]
 exact binary_clearing k _ _ _ _ _ hrel
theorem eliminatedCut_zero_iff {L:Type*} [Field L] (ev:Poly →+*L)
   (k:ℕ) (B:Fin (k+1) → Poly) (H G Q U:Poly) (t:K)
   (hN:ev (movingEquation H G Q U t)=0) (hH:ev H≠0) (hU:ev U≠0):
   ev (eliminatedCut k B Q U t)=0 ↔ ev (filteredCut k B H G)=0:=by
 have heq:=clearing_at_equation ev k B H G Q U t hN
 constructor
 · intro hz
   rw [hz,mul_zero] at heq
   exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hU)
 · intro hz
   rw [hz,mul_zero] at heq
   exact (mul_eq_zero.mp heq).resolve_left (pow_ne_zero _ hH)
theorem original_mem_of_eliminated_mem (P:Ideal Poly) [P.IsPrime]
   (k:ℕ) (B:Fin (k+1) → Poly) (H G Q U:Poly) (t:K)
   (hN:movingEquation H G Q U t∈P)
   (hT:eliminatedCut k B Q U t∈P) (hU:U∉P):
   filteredCut k B H G∈P:=by
 let ev:=Ideal.Quotient.mk P
 have heq:=clearing_at_equation ev k B H G Q U t
   (Ideal.Quotient.eq_zero_iff_mem.mpr hN)
 have hzero:ev (eliminatedCut k B Q U t)=0:=
   Ideal.Quotient.eq_zero_iff_mem.mpr hT
 have hUne:ev U≠0:=fun h↦hU (Ideal.Quotient.eq_zero_iff_mem.mp h)
 rw [hzero,mul_zero] at heq
 exact Ideal.Quotient.eq_zero_iff_mem.mp
   ((mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hUne))
theorem inFlag_const (p:FlagDegree) (c:K):PolynomialInFlag p (MvPolynomial.C c):=by
 intro d hd
 have hd0:d=0:=by
   by_contra h
   exact (MvPolynomial.mem_support_iff.mp hd) (MvPolynomial.coeff_C_of_ne_zero h _)
 subst d
 exact inFlag_zero p
private theorem flag_eq {p q:FlagDegree} (hx:p.zOnly=q.zOnly)
   (hy:p.yz=q.yz) (hz:p.all=q.all):p=q:=by
 cases p;cases q;simp_all
theorem inFlag_map {E:Type*} [Field E] (f:K →+*E)
   {p:FlagDegree} {A:Poly} (hA:PolynomialInFlag p A):
   PolynomialInFlag p (MvPolynomial.map f A):=by
 intro d hd
 exact hA d (MvPolynomial.support_map_subset f A hd)
theorem inFlag_sub_poly {p:FlagDegree} {A B:Poly}
   (hA:PolynomialInFlag p A) (hB:PolynomialInFlag p B):
   PolynomialInFlag p (A-B):=by
 intro d hd
 rcases Finset.mem_union.mp (MvPolynomial.support_sub (Fin 3) A B hd) with h | h
 · exact hA d h
 · exact hB d h
theorem inFlag_mul_poly {p q:FlagDegree} {A B:Poly}
   (hA:PolynomialInFlag p A) (hB:PolynomialInFlag q B):
   PolynomialInFlag (p+q) (A*B):=by
 intro d hd
 obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (MvPolynomial.support_mul A B hd)
 exact inFlag_add (hA a ha) (hB b hb)
theorem inFlag_pow_poly {p:FlagDegree} {A:Poly} (hA:PolynomialInFlag p A) (k:ℕ):
   PolynomialInFlag (k • p) (A^k):=by
 induction k with
 | zero => simpa using inFlag_const (0 • p) (1:K)
 | succ k ih =>
   have heq:(k+1) • p=k • p+p:=by
     apply flag_eq <;> simp only [nsmul_zOnly,nsmul_yz,nsmul_all,
       add_zOnly,add_yz,add_all] <;> ring
   rw [pow_succ,heq]
   exact inFlag_mul_poly ih hA
theorem inFlag_sum_poly {ι:Type*} (s:Finset ι) (p:FlagDegree) (A:ι → Poly)
   (hA:∀ i∈s,PolynomialInFlag p (A i)):PolynomialInFlag p (∑ i∈s,A i):=by
 intro d hd
 obtain ⟨i,hi,hdi⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
 exact hA i hi d hdi
theorem eliminatedCut_inFlag (k:ℕ) (B:Fin (k+1) → Poly) (Q U:Poly) (t:K)
   (c:Fin (k+1) → FlagDegree) (P:FlagDegree)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hQ:PolynomialInFlag (2 • unitAllFlag) Q)
   (hU:PolynomialInFlag unitYZFlag U)
   (hc:∀ j,c j+(k-j.val) • unitYZFlag+j.val • (2 • unitAllFlag)=P):
   PolynomialInFlag P (eliminatedCut k B Q U t):=by
 unfold eliminatedCut filteredCut
 apply inFlag_sum_poly
 intro j _
 rw [←hc j]
 exact inFlag_mul_poly (inFlag_mul_poly (hB j) (inFlag_pow_poly hU _))
   (inFlag_pow_poly (inFlag_sub_poly (inFlag_const _ _) hQ) _)
theorem eliminatedCut_small_flag (a b s k:ℕ) (C:FlagDegree)
   (B:Fin (k+1) → Poly) (Q U:Poly) (t:K)
   (c:Fin (k+1) → FlagDegree)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hQ:PolynomialInFlag (2 • unitAllFlag) Q)
   (hU:PolynomialInFlag unitYZFlag U)
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   PolynomialInFlag (C+k • (⟨a,b+1,s+2⟩:FlagDegree)) (eliminatedCut k B Q U t):=by
 apply eliminatedCut_inFlag k B Q U t c _ hB hQ hU
 intro j
 have hx:=congrArg FlagDegree.zOnly (hc j)
 have hy:=congrArg FlagDegree.yz (hc j)
 have hz:=congrArg FlagDegree.all (hc j)
 have hj:k-j.val+j.val=k:=Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)
 apply flag_eq
 all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,
   nsmul_all,unitYZFlag,unitAllFlag] at*
 all_goals nlinarith
theorem movingEquation_inFlag (a b s:ℕ) (H G Q U:Poly) (t:K)
   (hH:PolynomialInFlag ⟨a,b+1,s+1⟩ H)
   (hG:PolynomialInFlag ⟨a,b,s+3⟩ G)
   (hQ:PolynomialInFlag (2 • unitAllFlag) Q)
   (hU:PolynomialInFlag unitYZFlag U):
   PolynomialInFlag ⟨a,b+1,s+3⟩ (movingEquation H G Q U t):=by
 apply inFlag_sub_poly
 · have hc:(⟨a,b+1,s+1⟩:FlagDegree)+2 • unitAllFlag=⟨a,b+1,s+3⟩:=by
     apply flag_eq
     all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,
       nsmul_yz,nsmul_all,unitAllFlag]
     omega
   rw [←hc]
   exact inFlag_mul_poly hH (inFlag_sub_poly (inFlag_const _ _) hQ)
 · have hc:unitYZFlag+(⟨a,b,s+3⟩:FlagDegree)=⟨a,b+1,s+3⟩:=by
     apply flag_eq <;> simp only [add_zOnly,add_yz,add_all,unitYZFlag] <;> omega
   rw [←hc]
   exact inFlag_mul_poly hU hG
end
end ProximityPrize.SubmissionLower.RCN207
end PackedLegacy_D2

/-! Packed from ProximityPrize.SubmissionLower.Z8. -/
section PackedLegacy_Z8
namespace ProximityPrize.SubmissionLower.RCN198
open scoped Classical BigOperators
open RCN313 RCN136 RCN238 RCN053 RCN054 RCN095 RCN207 RCN234 RCN156 RCN275 RCN287
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
variable {K Ω:Type} [Field K] [Field Ω]
def direction (a b s:ℕ):FlagDegree:=⟨2*a,2*b+1,2*s+3⟩
def center (a b s:ℕ):FlagDegree:=unitYZFlag+direction a b s
def support (a b s:ℕ):ResidualSupportParameters:=
 ⟨s+2,b+s+3,a+b+s+3,by omega,by omega,by omega,by omega⟩
theorem shifted_flags (a b s:ℕ):
   hFlag a (b+1) (s+2)=⟨a,b+1,s+1⟩∧
   gFlag a (b+1) (s+2)=⟨a,b,s+3⟩∧
   directionFlag a (b+1) (s+2)=direction a b s:=by
 refine ⟨?_,?_,?_⟩ <;>
   simp only [hFlag,gFlag,directionFlag,direction] <;> congr 1 <;> omega
theorem class_total (a b s k:ℕ):
   unitYZFlag+(k+1) • direction a b s=
     center a b s+k • direction a b s:=by
 change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
 congr 1 <;> simp only [center,direction,unitYZFlag,
   add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all] <;> ring
theorem support_data (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3):
   ResidualSupportData (support a b s) F:=by
 refine ⟨?_,hYR,hAll⟩
 have hw:residualSWeights=Pi.single (2:Fin 4) 1:=by
   funext i;fin_cases i <;> rfl
 simpa only [hw,wt,support,MvPolynomial.weightedTotalDegree_piSingle] using hR
theorem sharp_flag_eq (a b s d:ℕ):
   sharpResidualAgreementFlag (support a b s) d=
     unitYZFlag+d • direction a b s:=by
 have hdir:sharpAgreementDirection (support a b s)=direction a b s:=by
   simp only [sharpAgreementDirection,support,direction]
   congr 1 <;> omega
 simp only [sharpResidualAgreementFlag,hdir,direction,unitYZFlag]
 change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
 congr 1 <;> simp only [add_zOnly,add_yz,add_all,
   nsmul_zOnly,nsmul_yz,nsmul_all] <;> ring
end
end ProximityPrize.SubmissionLower.RCN198
end PackedLegacy_Z8

/-! Packed from ProximityPrize.SubmissionLower.BZ. -/
section PackedLegacy_BZ
namespace ProximityPrize.SubmissionLower.RCN184
open scoped Classical BigOperators WithZero
open RCN187 RCN133 RCN295
noncomputable section
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
 [DecidableEq σ] [Algebra K L]
def coefficientEvaluation (x:σ → L) (E:Finset (σ →₀ ℕ)):
   (E → K) →ₗ[K] L where
 toFun c:=MvPolynomial.eval₂Hom (algebraMap K L) x
   (polynomialOfSupport E c)
 map_add' c d:=by
   rw [show polynomialOfSupport E (c+d)=
       polynomialOfSupport E c+polynomialOfSupport E d by
     ext m
     by_cases hm:m∈E <;>
       simp [coeff_polynomialOfSupport,hm]]
   exact map_add (MvPolynomial.eval₂Hom (algebraMap K L) x)
     (polynomialOfSupport E c) (polynomialOfSupport E d)
 map_smul' a c:=by
   rw [show polynomialOfSupport E (a • c)=
       a • polynomialOfSupport E c by
     ext m
     by_cases hm:m∈E <;>
       simp [coeff_polynomialOfSupport,hm]]
   simpa [Algebra.smul_def] using
     MvPolynomial.eval₂Hom_smul (algebraMap K L) x a
       (polynomialOfSupport E c)
def livePoleTruncation
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):σ →₀ ℕ:=
 d.filter (fun i↦x i≠0∧0 ≤ (v (x i)).log)
theorem livePoleTruncation_le
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):
   livePoleTruncation v x d ≤ d:=by
 intro i
 simp only [livePoleTruncation,Finsupp.filter_apply]
 split_ifs
 · exact le_rfl
 · exact Nat.zero_le _
theorem exponentValuationWeight_livePoleTruncation
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):
   exponentValuationWeight v x (livePoleTruncation v x d)=
     exponentPoleWeight v x d:=by
 classical
 unfold exponentValuationWeight exponentPoleWeight poleOrder
 apply Finset.sum_congr rfl
 intro i _
 simp only [livePoleTruncation,Finsupp.filter_apply]
 by_cases hx:x i=0
 · simp [hx]
 · by_cases hlog:0 ≤ (v (x i)).log
   · rw [if_pos ⟨hx,hlog⟩,max_eq_right hlog]
   · have hle:(v (x i)).log ≤ 0:=le_of_not_ge hlog
     rw [if_neg (fun h↦hlog h.2),max_eq_left hle]
     simp
theorem livePoleTruncation_coordinate_ne_zero
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ) (i:σ)
   (hi:livePoleTruncation v x d i≠0):x i≠0:=by
 classical
 simp only [livePoleTruncation,Finsupp.filter_apply] at hi
 split at hi
 · exact ‹x i≠0∧0 ≤ (v (x i)).log›.1
 · exact (hi rfl).elim
private theorem exp_sum (s:Finset σ) (z:σ → ℤ):
   WithZero.exp (∑ i∈s,z i)=∏ i∈s,WithZero.exp (z i):=by
 classical
 induction s using Finset.induction_on with
 | empty => simp
 | @insert i s hi ih => simp [hi,ih,WithZero.exp_add]
theorem valuation_eval_monomial_one_eq_exp
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ)
   (hlive:∀ i,d i≠0 → x i≠0):
   v (MvPolynomial.eval₂Hom (algebraMap K L) x
       (MvPolynomial.monomial d (1:K)))=
     WithZero.exp (exponentValuationWeight v x d):=by
 classical
 rw [MvPolynomial.eval₂Hom_monomial,
   Finsupp.prod_fintype _ _ (fun _↦pow_zero _),map_mul,map_prod]
 simp only [map_one,one_mul,map_pow]
 rw [show WithZero.exp (exponentValuationWeight v x d)=
     ∏ i,WithZero.exp ((d i:ℤ)*(v (x i)).log) by
   unfold exponentValuationWeight
   simpa only using exp_sum (Finset.univ:Finset σ)
     (fun i↦(d i:ℤ)*(v (x i)).log)]
 apply Finset.prod_congr rfl
 intro i _
 by_cases hd:d i=0
 · simp [hd]
 · have hvx:v (x i)≠0:=
     (Valuation.ne_zero_iff v).mpr (hlive i hd)
   rw [show ((d i:ℤ)*(v (x i)).log)=
       d i • (v (x i)).log by simp,
     WithZero.exp_nsmul,WithZero.exp_log hvx]
theorem exists_mem_exponentPoleWeight_eq
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)) (hzero:0∈E):
   ∃ d∈E,exponentPoleWeight v x d=exponentSetPoleWeight v x E:=by
 classical
 let S:=insert (0:ℤ) (E.image (exponentPoleWeight v x))
 have hS:S.Nonempty:=⟨0,Finset.mem_insert_self 0 _⟩
 have hmem:S.max' hS∈S:=Finset.max'_mem S hS
 change S.max' hS∈insert (0:ℤ) (E.image (exponentPoleWeight v x)) at hmem
 rcases Finset.mem_insert.mp hmem with hmax | hmax
 · refine ⟨0,hzero,?_⟩
   unfold exponentSetPoleWeight
   change exponentPoleWeight v x 0=S.max' hS
   simp only [exponentPoleWeight,Finsupp.zero_apply,Nat.cast_zero,
     zero_mul,Finset.sum_const_zero]
   exact hmax.symm
 · obtain ⟨d,hd,heq⟩:=Finset.mem_image.mp hmax
   refine ⟨d,hd,?_⟩
   unfold exponentSetPoleWeight
   change exponentPoleWeight v x d=S.max' hS
   exact heq
def deltaCoefficient (E:Finset (σ →₀ ℕ)) (e:E):E → K:=
 fun d↦if d=e then 1 else 0
theorem polynomialOfSupport_deltaCoefficient
   (E:Finset (σ →₀ ℕ)) (e:E):
   polynomialOfSupport E (deltaCoefficient E e:E → K)=
     MvPolynomial.monomial e.1 1:=by
 classical
 unfold polynomialOfSupport deltaCoefficient
 rw [Finset.sum_eq_single e]
 · simp
 · intro d _ hd
   simp [hd]
 · simp
theorem exists_exact_support_evaluation_of_downwardClosed
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   ∃ c:E → K,
     v (coefficientEvaluation x E c)=
       WithZero.exp (exponentSetPoleWeight v x E):=by
 obtain ⟨d,hd,hmax⟩:=exists_mem_exponentPoleWeight_eq v x E hzero
 let e:σ →₀ ℕ:=livePoleTruncation v x d
 have he:e∈E:=hdown d hd e (livePoleTruncation_le v x d)
 let esub:E:=⟨e,he⟩
 refine ⟨deltaCoefficient E esub,?_⟩
 rw [coefficientEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
   polynomialOfSupport_deltaCoefficient]
 rw [valuation_eval_monomial_one_eq_exp v x e
   (livePoleTruncation_coordinate_ne_zero v x d)]
 rw [exponentValuationWeight_livePoleTruncation,hmax]
theorem exponentSetPoleWeight_nonneg
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)):
   0 ≤ exponentSetPoleWeight v x E:=by
 unfold exponentSetPoleWeight
 exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
theorem poleOrder_eq_of_valuation_eq_exp
   (v:Valuation L (WithZero (Multiplicative ℤ))) (b:L) (q:ℤ)
   (hq:0 ≤ q) (hexact:v b=WithZero.exp q):
   poleOrder v b=q:=by
 unfold poleOrder
 rw [hexact,WithZero.log_exp,max_eq_right hq]
def cancellationSubmodule
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (hcoeff:∀ a:K,v (algebraMap K L a) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ)):
   Submodule K (E → K) where
 carrier:={c | v (coefficientEvaluation x E c) <
   WithZero.exp (exponentSetPoleWeight v x E)}
 zero_mem':=by
   change v (coefficientEvaluation x E 0) <
     WithZero.exp (exponentSetPoleWeight v x E)
   rw [map_zero,map_zero]
   exact WithZero.exp_pos
 add_mem':=by
   intro c d hc hd
   change v (coefficientEvaluation x E (c+d)) <
     WithZero.exp (exponentSetPoleWeight v x E)
   change v (coefficientEvaluation x E c) <
     WithZero.exp (exponentSetPoleWeight v x E) at hc
   change v (coefficientEvaluation x E d) <
     WithZero.exp (exponentSetPoleWeight v x E) at hd
   rw [map_add]
   exact (v.map_add _ _).trans_lt (max_lt hc hd)
 smul_mem':=by
   intro a c hc
   change v (coefficientEvaluation x E (a • c)) <
     WithZero.exp (exponentSetPoleWeight v x E)
   change v (coefficientEvaluation x E c) <
     WithZero.exp (exponentSetPoleWeight v x E) at hc
   rw [map_smul,Algebra.smul_def,map_mul]
   calc
     v (algebraMap K L a)*v (coefficientEvaluation x E c) ≤
         1*v (coefficientEvaluation x E c):=
       mul_le_mul' (hcoeff a) le_rfl
     _ < WithZero.exp (exponentSetPoleWeight v x E):=by
       simpa using hc
theorem cancellationSubmodule_ne_top_of_exact
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (hcoeff:∀ a:K,v (algebraMap K L a) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ))
   (c:E → K)
   (hc:v (coefficientEvaluation x E c)=
     WithZero.exp (exponentSetPoleWeight v x E)):
   cancellationSubmodule v hcoeff x E≠⊤:=by
 intro htop
 have hmem:c∈cancellationSubmodule v hcoeff x E:=by
   rw [htop]
   trivial
 change v (coefficientEvaluation x E c) <
   WithZero.exp (exponentSetPoleWeight v x E) at hmem
 rw [hc] at hmem
 exact (lt_irrefl _ hmem)
end
end ProximityPrize.SubmissionLower.RCN184
end PackedLegacy_BZ

/-! Packed from ProximityPrize.SubmissionLower.GA. -/
section PackedLegacy_GA
namespace ProximityPrize.SubmissionLower.RCN296
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN295 RCN344 RCN002 RCN005 RCN006 RCN007
noncomputable section
variable {K L σ:Type} [Field K] [Field L] [Fintype σ]
 [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
 [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place K L):=Classical.decEq _
variable (A:Type) [CommRing A] [IsDomain A]
 [Algebra K A] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) A L]
theorem finite_model_zero_points_le_exponentSet
   (x:σ → A) (E:Finset (σ →₀ ℕ))
   (F:MvPolynomial σ K) (hFE:F.support ⊆ E)
   (hF:MvPolynomial.eval₂Hom (algebraMap K A) x F≠0)
   (q:ℕ)
   (hpole:∀ W:Finset (Place K L),
     (∑ v∈W,exponentSetPoleWeight v.val
       (fun i↦algebraMap A L (x i)) E) ≤ (q:ℤ))
   (S:Finset (A →ₐ[K] K))
   (hS:∀ ψ∈S,ψ (MvPolynomial.eval₂Hom (algebraMap K A) x F)=0):
   S.card ≤ q:=by
 classical
 have heval:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦algebraMap A L (x i)) F=
       algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F):=
   (map_model_eval K L A x F).symm
 have hnonzero:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦algebraMap A L (x i)) F≠0:=by
   rw [heval]
   intro hz
   apply hF
   apply IsFractionRing.injective A L
   simpa only [map_zero] using hz
 let U:=S.image (modelPlace K L A)
 have hU:∀ v∈U,1 ≤ RCN026.order K L v
     (MvPolynomial.eval₂Hom (algebraMap K L)
       (fun i↦algebraMap A L (x i)) F):=by
   intro v hv
   obtain ⟨ψ,hψ,rfl⟩:=Finset.mem_image.mp hv
   rw [heval]
   exact RCN000.actual_model_zero_order_ge_one
     K A L ψ _ hF (hS ψ hψ)
 let W:=RCN026.placesFor K L _ hnonzero
 have hcount:=RCN026.finite_zero_places_le_poleMass
   K L _ hnonzero U hU
 have hsupport:=weighted_poleOrder_eval_le_exponentSet W
   (fun _↦1) (fun v↦v.val) (algebraMap K L)
   (fun v _ c↦constant_value_le_one K L v c)
   (fun i↦algebraMap A L (x i)) E F hFE
 have hcard:U.card=S.card:=
   Finset.card_image_of_injective _ (modelPlace_injective K L A)
 have hq:(S.card:ℤ) ≤ q:=by
   calc
     (S.card:ℤ)=(U.card:ℤ):=by rw [hcard]
     _ ≤ ∑ v∈W,RCN346.poleOrder K L v
         (MvPolynomial.eval₂Hom (algebraMap K L)
           (fun i↦algebraMap A L (x i)) F):=hcount
     _ ≤ ∑ v∈W,exponentSetPoleWeight v.val
         (fun i↦algebraMap A L (x i)) E:=by
       simpa only [RCN346.poleOrder,Nat.cast_one,one_mul] using hsupport
     _ ≤ (q:ℤ):=hpole W
 exact_mod_cast hq
section ActualCurve
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
end ActualCurve
end
end ProximityPrize.SubmissionLower.RCN296
end PackedLegacy_GA
end Compact_PackedLegacyCore2
