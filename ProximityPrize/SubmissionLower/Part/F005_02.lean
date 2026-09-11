import ProximityPrize.SubmissionLower.Part.F005_01
section Compact_PackedLegacyCore2
section PackedLegacy_GQ
namespace ProximityPrize.SubmissionLower.RCN317
open scoped Classical BigOperators
open RCN174 RCN319 RCN238 RCN266 RCN140 RCN291 RCN294 RCN318 RCN276 RCN141 RCN092
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota

def tightRegularCountCap (p:Profile):ℕ:=
 p.regularNumerator/p.gap^2
def tightFixedCountCap (p:Profile) (t:TightParameters):ℕ:=
 tightRegularCountCap p+t.countCap
def meetTightFixedCountCap:ℕ:=
 tightFixedCountCap meetProfile meetTightProfile
def meetTightFixedCost:ℕ:=meetTightFixedCountCap+1
end
end ProximityPrize.SubmissionLower.RCN317
end PackedLegacy_GQ

/-! Packed from ProximityPrize.SubmissionLower.AF. -/
section PackedLegacy_AF
namespace ProximityPrize.SubmissionLower.RCN287
open scoped Classical BigOperators
open RCN081 RCN313 RCN136 RCN234 RCN179 RCN095 RCN275 RCN275.ResidualSupportParameters RCN156 RCN174 RCN238 RCN266 RCN159 RCN164 RCN091 RCN276 RCN318 RCN141 RCN317
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
def sharpAgreementDirection (P:ResidualSupportParameters):FlagDegree:=
 ⟨2*(P.total-P.ys),2*(P.ys-P.s)-1,2*P.s-1⟩
def sharpResidualAgreementFlag
   (P:ResidualSupportParameters) (d:ℕ):FlagDegree:=
 ⟨(sharpAgreementDirection P).zOnly*d,
   1+(sharpAgreementDirection P).yz*d,
   (sharpAgreementDirection P).all*d⟩
theorem sharpResidualAgreementFlag_ys
   (P:ResidualSupportParameters) (hsy:P.s < P.ys) (d:ℕ):
   (sharpResidualAgreementFlag P d).yz+
       (sharpResidualAgreementFlag P d).all=
     1+d*(2*P.ys-2):=by
 have hcoeff:
     (2*(P.ys-P.s)-1)+(2*P.s-1)=2*P.ys-2:=by
   have hleft:1 ≤ 2*(P.ys-P.s):=by
     have:1 ≤ P.ys-P.s:=Nat.sub_pos_of_lt hsy
     omega
   have hright:1 ≤ 2*P.s:=by
     have:1 ≤ P.s:=P.one_le_s
     omega
   rw [tsub_add_tsub_comm hleft hright]
   have hsum:2*(P.ys-P.s)+2*P.s=2*P.ys:=by
     calc
       2*(P.ys-P.s)+2*P.s=2*((P.ys-P.s)+P.s):=by ring
       _=2*P.ys:=by rw [Nat.sub_add_cancel (Nat.le_of_lt hsy)]
   rw [hsum]
 simp only [sharpResidualAgreementFlag,sharpAgreementDirection]
 rw [←hcoeff]
 ring
theorem sharpResidualAgreementFlag_total
   (P:ResidualSupportParameters) (hsy:P.s < P.ys) (d:ℕ):
   (sharpResidualAgreementFlag P d).zOnly+
       (sharpResidualAgreementFlag P d).yz+
       (sharpResidualAgreementFlag P d).all=
     1+d*(2*P.total-2):=by
 have hcoeff:
     2*(P.total-P.ys)+(2*(P.ys-P.s)-1)+
         (2*P.s-1)=2*P.total-2:=by
   have hmiddle:
       (2*(P.ys-P.s)-1)+(2*P.s-1)=
         2*P.ys-2:=by
     have hleft:1 ≤ 2*(P.ys-P.s):=by
       have:1 ≤ P.ys-P.s:=Nat.sub_pos_of_lt hsy
       omega
     have hright:1 ≤ 2*P.s:=by
       have:1 ≤ P.s:=P.one_le_s
       omega
     rw [tsub_add_tsub_comm hleft hright]
     have hsum:2*(P.ys-P.s)+2*P.s=2*P.ys:=by
       calc
         2*(P.ys-P.s)+2*P.s=
             2*((P.ys-P.s)+P.s):=by ring
         _=2*P.ys:=by rw [Nat.sub_add_cancel (Nat.le_of_lt hsy)]
     rw [hsum]
   rw [Nat.add_assoc,hmiddle]
   have htwo:2 ≤ 2*P.ys:=by
     have:1 ≤ P.ys:=P.one_le_s.trans P.s_le_ys
     omega
   rw [←Nat.add_sub_assoc htwo]
   have hsum:2*(P.total-P.ys)+2*P.ys=2*P.total:=by
     calc
       2*(P.total-P.ys)+2*P.ys=
           2*((P.total-P.ys)+P.ys):=by ring
       _=2*P.total:=by rw [Nat.sub_add_cancel P.ys_le_total]
   rw [hsum]
 simp only [sharpResidualAgreementFlag,sharpAgreementDirection]
 rw [←hcoeff]
 ring
variable {K Omega:Type} [Field K] [Field Omega]
theorem sharp_agreement_weight_bounds
   {P:ResidualSupportParameters} {F:MvPolynomial (Fin 4) K}
   (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   (agreementNumerator F d coeffs x u0 u1).degreeOf (2:Fin 4) ≤
       d*(2*P.s-1)∧
     wt residualYSWeights (agreementNumerator F d coeffs x u0 u1) ≤
       1+d*(2*P.ys-2)∧
     wt residualTotalWeights (agreementNumerator F d coeffs x u0 u1) ≤
       1+d*(2*P.total-2):=by
 obtain ⟨hY,hR,hZ⟩:=H.coordinate_bounds
 refine ⟨(agreementNumerator_degree_bounds F P.ys P.s P.total
   P.one_le_s hY hR hZ d coeffs x u0 u1).2.1,?_,?_⟩
 · have h:=agreementNumerator_wt_le_equal_weight residualYSWeights rfl
     F P.ys (by change 1 ≤ 1;norm_num)
     (by change 1 ≤ P.ys;exact P.one_le_s.trans P.s_le_ys)
     (by change 2*1 ≤ P.ys;simpa using P.two_le_ys)
     (by change 1 ≤ 1;norm_num) H.ys_weight d coeffs x u0 u1
   have hcoeff:2*(P.ys-1)=2*P.ys-2:=by omega
   apply h.trans_eq
   change max 1 0+d*(2*(P.ys-1))=
     1+d*(2*P.ys-2)
   rw [hcoeff]
   norm_num
 · have htotalTwo:2 ≤ P.total:=P.two_le_ys.trans P.ys_le_total
   have honeTotal:1 ≤ P.total:=
     P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)
   have h:=agreementNumerator_wt_le_equal_weight residualTotalWeights rfl
     F P.total (by change 1 ≤ 1;norm_num)
     (by change 1 ≤ P.total;exact honeTotal)
     (by change 2*1 ≤ P.total;simpa using htotalTwo)
     (by change 1 ≤ 1;norm_num) H.total_weight d coeffs x u0 u1
   have hcoeff:2*(P.total-1)=2*P.total-2:=by omega
   apply h.trans_eq
   change max 1 1+d*(2*(P.total-1))=
     1+d*(2*P.total-2)
   rw [hcoeff]
   norm_num
theorem surfaceMap_agreement_in_sharp_flag
   {P:ResidualSupportParameters} (hsy:P.s < P.ys)
   (phi:Polynomial K →+*Omega) {F:MvPolynomial (Fin 4) K}
   (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   PolynomialInFlag (sharpResidualAgreementFlag P d)
     (surfaceMap phi (agreementNumerator F d coeffs x u0 u1)):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (support_surfaceMap_subset phi (agreementNumerator F d coeffs x u0 u1) he)
 obtain ⟨hR,hYS,hTotal⟩:=sharp_agreement_weight_bounds H
   d coeffs x u0 u1
 have hqR:=(MvPolynomial.monomial_le_degreeOf (2:Fin 4) hq).trans hR
 have hqYS:=
   (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS
 have hqTotal:=
   (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTotal
 rw [RCN081.weight_fin4] at hqYS hqTotal
 change q 0*0+q 1*1+q 2*1+q 3*0 ≤
   1+d*(2*P.ys-2) at hqYS
 change q 0*0+q 1*1+q 2*1+q 3*1 ≤
   1+d*(2*P.total-2) at hqTotal
 norm_num at hqYS hqTotal
 have hqR':q 2 ≤ (sharpResidualAgreementFlag P d).all:=by
   change q 2 ≤ (2*P.s-1)*d
   rw [Nat.mul_comm]
   exact hqR
 change q 2 ≤ (sharpResidualAgreementFlag P d).all∧
   q 1+q 2 ≤ (sharpResidualAgreementFlag P d).yz+
     (sharpResidualAgreementFlag P d).all∧
   q 1+q 2+q 3 ≤ (sharpResidualAgreementFlag P d).zOnly+
     (sharpResidualAgreementFlag P d).yz+
     (sharpResidualAgreementFlag P d).all
 refine ⟨hqR',?_,?_⟩
 · rw [sharpResidualAgreementFlag_ys P hsy]
   exact hqYS
 · rw [sharpResidualAgreementFlag_total P hsy]
   exact hqTotal
def factorRegularLedgerForDirection
   (p:Profile) (direction flag:FlagDegree):ℕ:=
 (flagMixed flag direction direction*p.degreeIncidence^2+
     2*flagMixed flag direction unitYZFlag*
       p.degreeIncidence*p.unitIncidence+
     flagMixed flag unitYZFlag unitYZFlag*p.unitIncidence^2)+
   (p.errors+1)*p.gap*
     (flagMixed flag direction unitZFlag*p.degreeIncidence+
       flagMixed flag unitYZFlag unitZFlag*p.unitIncidence)+
   (p.errors+1)*p.gap*
     (flagMixed flag direction unitAllFlag*p.degreeIncidence+
       flagMixed flag unitYZFlag unitAllFlag*p.unitIncidence)
def sharpRegularNumerator
   (p:Profile) (support:ResidualSupportParameters):ℕ:=
 factorRegularLedgerForDirection p (sharpAgreementDirection support)
   p.rectangularSurfaceFlag
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
def meetSharpFactorDegreeCost (flag:FlagDegree):ℕ:=
 (flagMixed flag (sharpAgreementDirection fixedMeetSupport)
       (sharpAgreementDirection fixedMeetSupport)*
     meetProfile.degreeIncidence+
   flagMixed flag (sharpAgreementDirection fixedMeetSupport) unitYZFlag*
     meetProfile.unitIncidence)+
 (meetProfile.errors+1)*meetProfile.gap*
   (flagMixed flag (sharpAgreementDirection fixedMeetSupport) unitZFlag+
     flagMixed flag (sharpAgreementDirection fixedMeetSupport) unitAllFlag)
def meetSharpFactorUnitCost (flag:FlagDegree):ℕ:=
 (flagMixed flag (sharpAgreementDirection fixedMeetSupport) unitYZFlag*
     meetProfile.degreeIncidence+
   flagMixed flag unitYZFlag unitYZFlag*meetProfile.unitIncidence)+
 (meetProfile.errors+1)*meetProfile.gap*
   (flagMixed flag unitYZFlag unitZFlag+
     flagMixed flag unitYZFlag unitAllFlag)
def meetSharpRegularNumerator:ℕ:=
 sharpRegularNumerator meetProfile fixedMeetSupport
def meetSharpTightFixedCountCap:ℕ:=
 meetSharpRegularNumerator/meetProfile.gap^2+
   meetTightProfile.countCap
def meetSharpTightFixedCost:ℕ:=meetSharpTightFixedCountCap+1
end
end ProximityPrize.SubmissionLower.RCN287
end PackedLegacy_AF

/-! Packed from ProximityPrize.SubmissionLower.N7. -/
section PackedLegacy_N7
namespace ProximityPrize.SubmissionLower.RCN262
open scoped BigOperators
open RCN077 RCN313 RCN293 RCN234 RCN179
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def vectorNumerator (F P:Poly K):Poly K :=
 polyH K F * MvPolynomial.pderiv (0:Fin 4) P +
   MvPolynomial.X (2:Fin 4) * polyH K F * MvPolynomial.pderiv (1:Fin 4) P +
   polyG K F * MvPolynomial.pderiv (2:Fin 4) P
theorem vectorNumerator_surface (F:Poly K):vectorNumerator F F = 0:=by
 unfold vectorNumerator polyG polyH
 ring
theorem vectorNumerator_mul (F P Q:Poly K) :
   vectorNumerator F (P * Q) = P * vectorNumerator F Q + Q * vectorNumerator F P:=by
 simp only [vectorNumerator,MvPolynomial.pderiv_mul]
 ring
theorem vectorNumerator_sub (F P Q:Poly K) :
   vectorNumerator F (P - Q) = vectorNumerator F P - vectorNumerator F Q:=by
 simp only [vectorNumerator,map_sub]
 ring
theorem numeratorStep_eq_vector (F P:Poly K) (b:ℕ) :
   numeratorStep K F b P =
     polyH K F * vectorNumerator F P -
       ((2 * b:ℕ):Poly K) * P * vectorNumerator F (polyH K F):=by
 unfold numeratorStep clearedStep vectorNumerator
 ring
theorem numeratorStep_sub (F P Q:Poly K) (b:ℕ) :
   numeratorStep K F b (P - Q) = numeratorStep K F b P - numeratorStep K F b Q:=by
 simp only [numeratorStep_eq_vector,vectorNumerator_sub]
 ring
theorem numeratorStep_mul_surface (F Q:Poly K) (b:ℕ) :
   numeratorStep K F b (F * Q) = F * numeratorStep K F b Q:=by
 simp only [numeratorStep_eq_vector,vectorNumerator_mul,vectorNumerator_surface,
   mul_zero,add_zero]
 ring
theorem numeratorStep_congr (F P Q:Poly K) (b:ℕ) (h:F ∣ P - Q) :
   F ∣ numeratorStep K F b P - numeratorStep K F b Q:=by
 obtain ⟨T,hT⟩:=h
 refine ⟨numeratorStep K F b T,?_⟩
 rw [← numeratorStep_sub,hT,numeratorStep_mul_surface]
theorem vectorNumerator_R_degree_bound (F P:Poly K) (a s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (hP:P.degreeOf (2:Fin 4) ≤ a) :
   (vectorNumerator F P).degreeOf (2:Fin 4) ≤ a + s:=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf (2:Fin 4) ≤ 1:=by simp [R]
 have hH:H.degreeOf (2:Fin 4) ≤ s - 1 :=
   pderiv_same_degree_bound (2:Fin 4) F s hF
 have hG:G.degreeOf (2:Fin 4) ≤ s + 1 :=
   polyG_degree_bound (2:Fin 4) F s 1 hF hR
 have hPX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) P a hP
 have hPY:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) P a hP
 have hPR:=pderiv_same_degree_bound (2:Fin 4) P a hP
 have hx:(H * MvPolynomial.pderiv (0:Fin 4) P).degreeOf (2:Fin 4) ≤ a + s:=by
   have h:=degree_mul_bound (2:Fin 4) hH hPX
   omega
 have hy:(R * H * MvPolynomial.pderiv (1:Fin 4) P).degreeOf (2:Fin 4) ≤ a + s:=by
   have h:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hR hH) hPY
   omega
 have hr:(G * MvPolynomial.pderiv (2:Fin 4) P).degreeOf (2:Fin 4) ≤ a + s:=by
   by_cases ha:a = 0
   · have hz:=pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) P (by simpa [ha] using hP)
     simp [hz]
   · have h:=degree_mul_bound (2:Fin 4) hG hPR
     omega
 exact degree_add_bound (2:Fin 4) (degree_add_bound (2:Fin 4) hx hy) hr
theorem pderiv_eq_zero_of_wt_lt (weights:Fin 4 → ℕ) (P:Poly K) (i:Fin 4)
   (hP:wt weights P < weights i):MvPolynomial.pderiv i P = 0:=by
 apply MvPolynomial.support_eq_empty.mp
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro d hd
 have hh:=MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i P d hd)
 simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
 change Finsupp.weight weights d + weights i ≤ wt weights P at hh
 omega
def excessFactor (F P:Poly K) (s b:ℕ):Poly K :=
 (s:Poly K) *
   ((s:Poly K) * liftedCoefficient F s *
       MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient P (2 * b * (s - 1))) -
     ((2 * b * (s - 1) + 2 * b:ℕ):Poly K) *
       MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s) *
         liftedCoefficient P (2 * b * (s - 1)))
def reductionMultiplier (F P:Poly K) (s b:ℕ):Poly K :=
 excessFactor F P s b * MvPolynomial.X (2:Fin 4) ^ ((2 * b + 1) * (s - 1))
def reducedStep (F P:Poly K) (s b:ℕ):Poly K :=
 numeratorStep K F b P - reductionMultiplier F P s b * F
def reducedNumerator (F:Poly K) (s:ℕ):ℕ → Poly K
 | 0 => MvPolynomial.X (1:Fin 4)
 | b + 1 => reducedStep F (reducedNumerator F s b) s b
@[simp] theorem reducedNumerator_zero (F:Poly K) (s:ℕ) :
   reducedNumerator F s 0 = MvPolynomial.X (1:Fin 4):=rfl
@[simp] theorem reducedNumerator_succ (F:Poly K) (s b:ℕ) :
   reducedNumerator F s (b + 1) = reducedStep F (reducedNumerator F s b) s b:=rfl
theorem numerator_sub_reduced_dvd (F:Poly K) (s b:ℕ) :
   F ∣ numerator K F b - reducedNumerator F s b:=by
 induction b with
 | zero => simp
 | succ b ih =>
     have hstep:=numeratorStep_congr F (numerator K F b) (reducedNumerator F s b) b ih
     obtain ⟨T,hT⟩:=hstep
     refine ⟨T + reductionMultiplier F (reducedNumerator F s b) s b,?_⟩
     rw [numerator_succ,reducedNumerator_succ,reducedStep]
     linear_combination hT
def reducedCommonNumeratorTerm (F:Poly K) (s w:ℕ) (c:ℕ → K) (x:K)
   (j:ℕ):Poly K :=
 MvPolynomial.C (c j) * reducedNumerator F s j *
   polyH K F ^ (2 * (w - j)) *
     (MvPolynomial.C x - MvPolynomial.X (0:Fin 4)) ^ j
def reducedClearedTaylorNumerator (F:Poly K) (s w:ℕ) (c:ℕ → K) (x:K) :
   Poly K :=
 ∑ j ∈ Finset.range (w + 1),reducedCommonNumeratorTerm F s w c x j
def reducedAgreementNumerator (F:Poly K) (s w:ℕ) (c:ℕ → K) (x u₀ u₁:K) :
   Poly K :=
 reducedClearedTaylorNumerator F s w c x -
   affineSeedPolynomial u₀ u₁ * polyH K F ^ (2 * w)
theorem commonNumeratorTerm_sub_reduced_dvd (F:Poly K) (s w j:ℕ)
   (c:ℕ → K) (x:K) :
   F ∣ commonNumeratorTerm F w c x j - reducedCommonNumeratorTerm F s w c x j:=by
 obtain ⟨T,hT⟩:=numerator_sub_reduced_dvd F s j
 refine ⟨MvPolynomial.C (c j) * T * polyH K F ^ (2 * (w - j)) *
   (MvPolynomial.C x - MvPolynomial.X (0:Fin 4)) ^ j,?_⟩
 unfold commonNumeratorTerm reducedCommonNumeratorTerm
 linear_combination MvPolynomial.C (c j) * polyH K F ^ (2 * (w - j)) *
   (MvPolynomial.C x - MvPolynomial.X (0:Fin 4)) ^ j * hT
theorem clearedTaylorNumerator_sub_reduced_dvd (F:Poly K) (s w:ℕ)
   (c:ℕ → K) (x:K) :
   F ∣ clearedTaylorNumerator F w c x - reducedClearedTaylorNumerator F s w c x:=by
 unfold clearedTaylorNumerator reducedClearedTaylorNumerator
 rw [← Finset.sum_sub_distrib]
 exact Finset.dvd_sum fun j _ => commonNumeratorTerm_sub_reduced_dvd F s w j c x
theorem agreementNumerator_sub_reduced_dvd (F:Poly K) (s w:ℕ)
   (c:ℕ → K) (x u₀ u₁:K) :
   F ∣ agreementNumerator F w c x u₀ u₁ -
     reducedAgreementNumerator F s w c x u₀ u₁:=by
 unfold agreementNumerator reducedAgreementNumerator
 simpa only [sub_sub_sub_cancel_right] using
   clearedTaylorNumerator_sub_reduced_dvd F s w c x
end
end ProximityPrize.SubmissionLower.RCN262
end PackedLegacy_N7

/-! Packed from ProximityPrize.SubmissionLower.N6. -/
section PackedLegacy_N6
namespace ProximityPrize.SubmissionLower.RCN261
open RCN290 RCN293 RCN081
noncomputable section
variable {K:Type*} [Field K]
theorem embedCoefficients_injective:Function.Injective (embedCoefficients K):=by
 intro P Q h
 exact Polynomial.C_injective ((collectR K).symm.injective h)
@[simp] theorem liftedCoefficient_zero (n:ℕ) :
   liftedCoefficient (0:MvPolynomial (Fin 4) K) n = 0:=by
 simp [liftedCoefficient]
@[simp] theorem liftedCoefficient_add (P Q:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (P + Q) n = liftedCoefficient P n + liftedCoefficient Q n:=by
 simp [liftedCoefficient]
@[simp] theorem liftedCoefficient_sub (P Q:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (P - Q) n = liftedCoefficient P n - liftedCoefficient Q n:=by
 simp [liftedCoefficient]
@[simp] theorem liftedCoefficient_neg (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (-P) n = -liftedCoefficient P n:=by
 simp [liftedCoefficient]
theorem liftedCoefficient_eq_zero_iff (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient P n = 0 ↔ (collectR K P).coeff n = 0:=by
 change embedCoefficients K ((collectR K P).coeff n) = 0 ↔ _
 rw [← map_zero (embedCoefficients K),embedCoefficients_injective.eq_iff]
theorem liftedCoefficient_eq_zero_of_degree_lt (P:MvPolynomial (Fin 4) K)
   (n:ℕ) (hP:P.degreeOf 2 < n):liftedCoefficient P n = 0:=by
 apply (liftedCoefficient_eq_zero_iff P n).mpr
 exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [collectR_natDegree])
theorem collectR_X_R :
   collectR K (MvPolynomial.X (2:Fin 4)) = Polynomial.X:=by
 simp [collectR,MvPolynomial.renameEquiv_apply,
   Equiv.optionSubtypeNe_symm_apply]
theorem collectR_pderiv_R (P:MvPolynomial (Fin 4) K) :
   collectR K (MvPolynomial.pderiv (2:Fin 4) P) = (collectR K P).derivative:=by
 classical
 induction P using MvPolynomial.induction_on with
 | C c =>
     simp [collectR,MvPolynomial.renameEquiv_apply]
 | add P Q hP hQ => simp only [map_add,hP,hQ]
 | mul_X P i hP =>
     by_cases hi:i = 2
     · subst i
       simp [map_mul,collectR_X_R,Polynomial.derivative_mul,hP]
       ring
     · have hX:=collectR_X_other (K:=K) (⟨i,hi⟩:RemainingCoordinates)
       simp only [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X_of_ne hi,
         mul_zero,add_zero,map_mul,hX,Polynomial.derivative_mul,
         Polynomial.derivative_C,mul_zero,add_zero,hP]
theorem liftedCoefficient_pderiv_R (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (MvPolynomial.pderiv (2:Fin 4) P) n =
     MvPolynomial.C ((n + 1:ℕ):K) * liftedCoefficient P (n + 1):=by
 unfold liftedCoefficient
 rw [collectR_pderiv_R,Polynomial.coeff_derivative,map_mul]
 simp only [map_add,map_natCast,map_one,Nat.cast_add,Nat.cast_one]
 ring
private theorem optionCoefficient_pderiv_some {σ:Type*}
   (P:MvPolynomial (Option σ) K) (i:σ) (n:ℕ) :
   (MvPolynomial.optionEquivLeft K σ (MvPolynomial.pderiv (some i) P)).coeff n =
     MvPolynomial.pderiv i ((MvPolynomial.optionEquivLeft K σ P).coeff n):=by
 classical
 ext e
 rw [MvPolynomial.optionEquivLeft_coeff_coeff,MvPolynomial.coeff_pderiv,
   MvPolynomial.coeff_pderiv,MvPolynomial.optionEquivLeft_coeff_coeff]
 have he:e.optionElim n + Finsupp.single (some i) 1 =
     (e + Finsupp.single i 1).optionElim n:=by
   ext j
   cases j with
   | none => simp
   | some j =>
       simp only [Finsupp.add_apply,Finsupp.optionElim_apply_some]
       rw [Finsupp.single_apply_left
         (show Function.Injective (some:σ → Option σ) from fun _ _ h => Option.some.inj h)]
 rw [he,Finsupp.optionElim_apply_some]
theorem liftedCoefficient_pderiv_other (P:MvPolynomial (Fin 4) K)
   (i:Fin 4) (hi:i ≠ 2) (n:ℕ) :
   liftedCoefficient (MvPolynomial.pderiv i P) n =
     MvPolynomial.pderiv i (liftedCoefficient P n):=by
 have hindex:(Equiv.optionSubtypeNe (2:Fin 4)).symm i = some ⟨i,hi⟩:=by
   simp [Equiv.optionSubtypeNe_symm_apply,hi]
 have hrename :
     MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm
       (MvPolynomial.pderiv i P) =
     MvPolynomial.pderiv (some (⟨i,hi⟩:RemainingCoordinates))
       (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm P):=by
   rw [← MvPolynomial.pderiv_rename
     (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective i P,hindex]
 have hc:(collectR K (MvPolynomial.pderiv i P)).coeff n =
     MvPolynomial.pderiv (⟨i,hi⟩:RemainingCoordinates) ((collectR K P).coeff n):=by
   change (MvPolynomial.optionEquivLeft K RemainingCoordinates
     (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm
       (MvPolynomial.pderiv i P))).coeff n = _
   rw [hrename,optionCoefficient_pderiv_some]
   rfl
 unfold liftedCoefficient
 rw [hc,embedCoefficients_eq_rename,embedCoefficients_eq_rename]
 exact (MvPolynomial.pderiv_rename Subtype.val_injective
   (⟨i,hi⟩:RemainingCoordinates) ((collectR K P).coeff n)).symm
theorem liftedCoefficient_pderiv_R_top (P:MvPolynomial (Fin 4) K) (a:ℕ)
   (ha:0 < a) :
   liftedCoefficient (MvPolynomial.pderiv (2:Fin 4) P) (a - 1) =
     MvPolynomial.C (a:K) * liftedCoefficient P a:=by
 simpa only [Nat.sub_add_cancel ha] using liftedCoefficient_pderiv_R P (a - 1)
theorem liftedCoefficient_mul_top (P Q:MvPolynomial (Fin 4) K) (a b:ℕ)
   (hP:P.degreeOf 2 ≤ a) (hQ:Q.degreeOf 2 ≤ b) :
   liftedCoefficient (P * Q) (a + b) =
     liftedCoefficient P a * liftedCoefficient Q b:=by
 unfold liftedCoefficient
 rw [map_mul,Polynomial.coeff_mul_add_eq_of_natDegree_le
   (by rwa [collectR_natDegree]) (by rwa [collectR_natDegree]),map_mul]
theorem liftedCoefficient_zero_degree (P:MvPolynomial (Fin 4) K)
   (hP:P.degreeOf 2 = 0):liftedCoefficient P 0 = P:=by
 have hC:collectR K P = Polynomial.C ((collectR K P).coeff 0) :=
   Polynomial.eq_C_of_natDegree_eq_zero (by rwa [collectR_natDegree])
 change (collectR K).symm (Polynomial.C ((collectR K P).coeff 0)) = P
 rw [← hC,AlgEquiv.symm_apply_apply]
theorem liftedCoefficient_mul_degree_zero_left (P Q:MvPolynomial (Fin 4) K)
   (n:ℕ) (hP:P.degreeOf 2 = 0) :
   liftedCoefficient (P * Q) n = P * liftedCoefficient Q n:=by
 have hC:collectR K P = Polynomial.C ((collectR K P).coeff 0) :=
   Polynomial.eq_C_of_natDegree_eq_zero (by rwa [collectR_natDegree])
 unfold liftedCoefficient
 rw [map_mul,hC,Polynomial.coeff_C_mul,map_mul]
 change liftedCoefficient P 0 * _ = _
 rw [liftedCoefficient_zero_degree P hP]
@[simp] theorem liftedCoefficient_C_mul (c:K) (P:MvPolynomial (Fin 4) K)
   (n:ℕ):liftedCoefficient (MvPolynomial.C c * P) n =
     MvPolynomial.C c * liftedCoefficient P n :=
 liftedCoefficient_mul_degree_zero_left _ P n (MvPolynomial.degreeOf_C c 2)
@[simp] theorem liftedCoefficient_natCast_mul (c:ℕ)
   (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient ((c:MvPolynomial (Fin 4) K) * P) n =
     (c:MvPolynomial (Fin 4) K) * liftedCoefficient P n:=by
 simpa only [map_natCast] using liftedCoefficient_C_mul (c:K) P n
theorem liftedCoefficient_X_R_pow (n:ℕ) :
   liftedCoefficient ((MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K) ^ n) n =
     1:=by
 simp [liftedCoefficient,map_pow,collectR_X_R]
theorem liftedCoefficient_X_R_mul (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (MvPolynomial.X (2:Fin 4) * P) (n + 1) =
     liftedCoefficient P n:=by
 unfold liftedCoefficient
 rw [map_mul,collectR_X_R,Polynomial.coeff_X_mul]
theorem liftedCoefficient_support_exact
   (P:MvPolynomial (Fin 4) K) (n:ℕ) (e:Fin 4 →₀ ℕ)
   (he:e ∈ (liftedCoefficient P n).support) :
   ∃ d ∈ P.support,d 2 = n ∧ e 2 = 0 ∧ ∀ i,i ≠ 2 → e i = d i:=by
 classical
 have heR:e 2 = 0:=by
   have hh:=MvPolynomial.monomial_le_degreeOf (2:Fin 4) he
   rw [liftedCoefficient_R_degree] at hh
   omega
 change e ∈ (embedCoefficients K ((collectR K P).coeff n)).support at he
 rw [embedCoefficients_eq_rename,
   MvPolynomial.support_rename_of_injective Subtype.val_injective] at he
 obtain ⟨u,hu,heu⟩:=Finset.mem_image.mp he
 have hopt:u.optionElim n ∈
     (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm P).support :=
   (MvPolynomial.mem_support_coeff_optionEquivLeft (R:=K)).mp hu
 rw [MvPolynomial.support_rename_of_injective
   (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at hopt
 obtain ⟨d,hd,hdu⟩:=Finset.mem_image.mp hopt
 refine ⟨d,hd,?_,heR,?_⟩
 · have huv:=congrArg
     (fun f:Option RemainingCoordinates →₀ ℕ =>
       f ((Equiv.optionSubtypeNe (2:Fin 4)).symm 2)) hdu
   rw [Finsupp.mapDomain_apply (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at huv
   simpa [Equiv.optionSubtypeNe_symm_apply] using huv
 · intro i hi
   have hev:e i = u ⟨i,hi⟩:=by
     rw [← heu]
     exact Finsupp.mapDomain_apply Subtype.val_injective u ⟨i,hi⟩
   have huv:=congrArg
     (fun f:Option RemainingCoordinates →₀ ℕ =>
       f ((Equiv.optionSubtypeNe (2:Fin 4)).symm i)) hdu
   rw [Finsupp.mapDomain_apply (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at huv
   have hindex:(Equiv.optionSubtypeNe (2:Fin 4)).symm i = some ⟨i,hi⟩:=by
     simp [Equiv.optionSubtypeNe_symm_apply,hi]
   rw [hindex,Finsupp.optionElim_apply_some] at huv
   exact hev.trans huv.symm
theorem liftedCoefficient_weight_add_le (weights:Fin 4 → ℕ)
   (P:MvPolynomial (Fin 4) K) (n:ℕ) (hn:liftedCoefficient P n ≠ 0) :
   MvPolynomial.weightedTotalDegree weights (liftedCoefficient P n) + n * weights 2 ≤
     MvPolynomial.weightedTotalDegree weights P:=by
 classical
 obtain ⟨e,he,hmax⟩:=Finset.exists_mem_eq_sup
   (liftedCoefficient P n).support (MvPolynomial.support_nonempty.mpr hn)
   (Finsupp.weight weights)
 obtain ⟨d,hd,hdR,heR,heq⟩:=liftedCoefficient_support_exact P n e he
 have hw:Finsupp.weight weights e + n * weights 2 = Finsupp.weight weights d:=by
   rw [weight_fin4,weight_fin4,hdR,heR,
     heq 0 (by decide),heq 1 (by decide),heq 3 (by decide)]
   omega
 change (liftedCoefficient P n).support.sup (Finsupp.weight weights) + _ ≤ _
 rw [hmax,hw]
 exact MvPolynomial.le_weightedTotalDegree weights hd
theorem liftedCoefficient_weight_le_sub (weights:Fin 4 → ℕ)
   (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   MvPolynomial.weightedTotalDegree weights (liftedCoefficient P n) ≤
     MvPolynomial.weightedTotalDegree weights P - n * weights 2:=by
 by_cases hn:liftedCoefficient P n = 0
 · simp [hn,MvPolynomial.weightedTotalDegree]
 · have h:=liftedCoefficient_weight_add_le weights P n hn
   omega
theorem degreeR_le_sub_one_of_top_zero (P:MvPolynomial (Fin 4) K) (t:ℕ)
   (ht:0 < t) (hP:P.degreeOf 2 ≤ t) (hzero:liftedCoefficient P t = 0) :
   P.degreeOf 2 ≤ t - 1:=by
 rw [← collectR_natDegree]
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro n hn
 by_cases heq:n = t
 · subst n
   exact (liftedCoefficient_eq_zero_iff P t).mp hzero
 · exact Polynomial.coeff_eq_zero_of_natDegree_lt
     (by rw [collectR_natDegree]; omega)
theorem degreeR_sub_cancel_top (W F q:MvPolynomial (Fin 4) K) (t s k:ℕ)
   (ht:0 < t) (hW:W.degreeOf 2 ≤ t) (hF:F.degreeOf 2 ≤ s)
   (hq:q.degreeOf 2 = 0) (hks:k + s = t)
   (hcoeff:liftedCoefficient W t = q * liftedCoefficient F s) :
   (W - q * MvPolynomial.X (2:Fin 4) ^ k * F).degreeOf 2 ≤ t - 1:=by
 have hR:((MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K) ^ k).degreeOf 2 ≤ k:=by
   simpa using MvPolynomial.degreeOf_pow_le (2:Fin 4)
     (MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K) k
 have hqR:(q * MvPolynomial.X (2:Fin 4) ^ k).degreeOf 2 ≤ k:=by
   have h:=MvPolynomial.degreeOf_mul_le (2:Fin 4) q
     ((MvPolynomial.X (2:Fin 4)) ^ k)
   omega
 have hprod:(q * MvPolynomial.X (2:Fin 4) ^ k * F).degreeOf 2 ≤ t:=by
   have h:=RCN313.degree_mul_bound (2:Fin 4) hqR hF
   omega
 apply degreeR_le_sub_one_of_top_zero _ t ht
   (RCN313.degree_sub_bound (2:Fin 4) hW hprod)
 rw [liftedCoefficient_sub,← hks,
   liftedCoefficient_mul_top _ F k s hqR hF,
   liftedCoefficient_mul_degree_zero_left _ _ k hq,
   liftedCoefficient_X_R_pow,mul_one,hks,hcoeff,sub_self]
end
end ProximityPrize.SubmissionLower.RCN261
end PackedLegacy_N6

/-! Packed from ProximityPrize.SubmissionLower.N8. -/
section PackedLegacy_N8
namespace ProximityPrize.SubmissionLower.RCN262
open scoped BigOperators
open RCN077 RCN313 RCN293 RCN261
noncomputable section
set_option maxHeartbeats 800000
variable {K:Type*} [Field K]
theorem liftedCoefficient_polyH_top (F:Poly K) (s:ℕ) (hs:1 ≤ s) :
   liftedCoefficient (polyH K F) (s - 1) = (s:Poly K) * liftedCoefficient F s:=by
 simpa only [polyH,map_natCast] using liftedCoefficient_pderiv_R_top F s hs
theorem liftedCoefficient_polyG_top (F:Poly K) (s:ℕ)
   (hF:F.degreeOf (2:Fin 4) ≤ s) :
   liftedCoefficient (polyG K F) (s + 1) =
     -MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s):=by
 have hPX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) F s hF
 have hx:liftedCoefficient (MvPolynomial.pderiv (0:Fin 4) F) (s + 1) = 0 :=
   liftedCoefficient_eq_zero_of_degree_lt _ _ (by omega)
 simp only [polyG,liftedCoefficient_neg,liftedCoefficient_add,hx,zero_add,
   liftedCoefficient_X_R_mul,liftedCoefficient_pderiv_other F 1 (by decide) s]
theorem vectorNumerator_top_coefficient (F P:Poly K) (a s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (hP:P.degreeOf (2:Fin 4) ≤ a) :
   liftedCoefficient (vectorNumerator F P) (a + s) =
     (s:Poly K) * liftedCoefficient F s *
         MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient P a) -
       (a:Poly K) * MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s) *
         liftedCoefficient P a:=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf (2:Fin 4) ≤ 1:=by simp [R]
 have hH:H.degreeOf (2:Fin 4) ≤ s - 1 :=
   pderiv_same_degree_bound (2:Fin 4) F s hF
 have hG:G.degreeOf (2:Fin 4) ≤ s + 1 :=
   polyG_degree_bound (2:Fin 4) F s 1 hF hR
 have hPX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) P a hP
 have hPY:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) P a hP
 have hPR:=pderiv_same_degree_bound (2:Fin 4) P a hP
 have hcR:liftedCoefficient R 1 = 1:=by
   simpa only [R,pow_one] using liftedCoefficient_X_R_pow (K:=K) 1
 have hcH:liftedCoefficient H (s - 1) = (s:Poly K) * liftedCoefficient F s :=
   liftedCoefficient_polyH_top F s hs
 have hRH:(R * H).degreeOf (2:Fin 4) ≤ s:=by
   have h:=degree_mul_bound (2:Fin 4) hR hH
   omega
 have hcRH:liftedCoefficient (R * H) s = (s:Poly K) * liftedCoefficient F s:=by
   have h:=liftedCoefficient_mul_top R H 1 (s - 1) hR hH
   rw [show 1 + (s - 1) = s by omega,hcR,hcH,one_mul] at h
   exact h
 have hx:liftedCoefficient (H * MvPolynomial.pderiv (0:Fin 4) P) (a + s) = 0:=by
   apply liftedCoefficient_eq_zero_of_degree_lt
   have h:=degree_mul_bound (2:Fin 4) hH hPX
   omega
 have hy:liftedCoefficient (R * H * MvPolynomial.pderiv (1:Fin 4) P) (a + s) =
     (s:Poly K) * liftedCoefficient F s *
       MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient P a):=by
   have h:=liftedCoefficient_mul_top (R * H) (MvPolynomial.pderiv (1:Fin 4) P)
     s a hRH hPY
   rw [hcRH,liftedCoefficient_pderiv_other P 1 (by decide) a] at h
   simpa only [Nat.add_comm] using h
 have hr:liftedCoefficient (G * MvPolynomial.pderiv (2:Fin 4) P) (a + s) =
     -(a:Poly K) * MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s) *
       liftedCoefficient P a:=by
   by_cases ha:a = 0
   · have hz:=pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) P (by simpa [ha] using hP)
     simp [ha,hz]
   · have hapos:0 < a:=Nat.pos_of_ne_zero ha
     have h:=liftedCoefficient_mul_top G (MvPolynomial.pderiv (2:Fin 4) P)
       (s + 1) (a - 1) hG hPR
     rw [show s + 1 + (a - 1) = a + s by omega,
       liftedCoefficient_polyG_top F s hF,
       liftedCoefficient_pderiv_R_top P a hapos,map_natCast] at h
     rw [h]
     ring
 change liftedCoefficient (H * MvPolynomial.pderiv (0:Fin 4) P +
   R * H * MvPolynomial.pderiv (1:Fin 4) P +
     G * MvPolynomial.pderiv (2:Fin 4) P) (a + s) = _
 rw [liftedCoefficient_add,liftedCoefficient_add,hx,hy,hr]
 ring
theorem vectorNumerator_H_top_coefficient (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s) :
   liftedCoefficient (vectorNumerator F (polyH K F)) (2 * s - 1) =
     (s:Poly K) * liftedCoefficient F s *
       MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s):=by
 have hH:=pderiv_same_degree_bound (2:Fin 4) F s hF
 have h:=vectorNumerator_top_coefficient F (polyH K F) (s - 1) s hs hF hH
 rw [show s - 1 + s = 2 * s - 1 by omega,
   liftedCoefficient_polyH_top F s hs] at h
 rw [h,MvPolynomial.pderiv_mul]
 simp only [Derivation.map_natCast,zero_mul,mul_zero,add_zero,zero_add]
 rw [Nat.cast_sub hs]
 simp only [Nat.cast_one]
 ring
theorem numeratorStep_top_coefficient (F P:Poly K) (a s b:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (hP:P.degreeOf (2:Fin 4) ≤ a) :
   liftedCoefficient (numeratorStep K F b P) (a + (2 * s - 1)) =
     liftedCoefficient F s * ((s:Poly K) *
       ((s:Poly K) * liftedCoefficient F s *
           MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient P a) -
         ((a + 2 * b:ℕ):Poly K) *
           MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s) *
             liftedCoefficient P a)):=by
 have hH:=pderiv_same_degree_bound (2:Fin 4) F s hF
 have hV:=vectorNumerator_R_degree_bound F P a s hs hF hP
 have hVH:(vectorNumerator F (polyH K F)).degreeOf (2:Fin 4) ≤ 2 * s - 1:=by
   have h:=vectorNumerator_R_degree_bound F (polyH K F) (s - 1) s hs hF hH
   omega
 have hfirst:=liftedCoefficient_mul_top (polyH K F) (vectorNumerator F P)
   (s - 1) (a + s) hH hV
 rw [show s - 1 + (a + s) = a + (2 * s - 1) by omega,
   liftedCoefficient_polyH_top F s hs,
   vectorNumerator_top_coefficient F P a s hs hF hP] at hfirst
 have hlast:=liftedCoefficient_mul_top P (vectorNumerator F (polyH K F))
   a (2 * s - 1) hP hVH
 rw [vectorNumerator_H_top_coefficient F s hs hF] at hlast
 rw [numeratorStep_eq_vector,liftedCoefficient_sub,hfirst]
 rw [show ((2 * b:ℕ):Poly K) * P * vectorNumerator F (polyH K F) =
   ((2 * b:ℕ):Poly K) * (P * vectorNumerator F (polyH K F)) by ring,
   liftedCoefficient_natCast_mul,hlast]
 push_cast
 ring
theorem excessFactor_R_degree (F P:Poly K) (s b:ℕ) :
   (excessFactor F P s b).degreeOf (2:Fin 4) = 0:=by
 have hf:(liftedCoefficient F s).degreeOf (2:Fin 4) ≤ 0 :=
   (liftedCoefficient_R_degree F s).le
 have hc:(liftedCoefficient P (2 * b * (s - 1))).degreeOf (2:Fin 4) ≤ 0 :=
   (liftedCoefficient_R_degree P _).le
 have hdf:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) _ 0 hf
 have hdc:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) _ 0 hc
 have hs:(s:Poly K).degreeOf (2:Fin 4) ≤ 0:=(degree_natCast_eq_zero 2 s).le
 have hn:((2 * b * (s - 1) + 2 * b:ℕ):Poly K).degreeOf (2:Fin 4) ≤ 0 :=
   (degree_natCast_eq_zero 2 _).le
 have hleft:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hs hf) hdc
 have hright:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hn hdf) hc
 have hinner:=degree_sub_bound (2:Fin 4) hleft hright
 have h:=degree_mul_bound (2:Fin 4) hs hinner
 exact Nat.eq_zero_of_le_zero (by simpa only [excessFactor,Nat.zero_add] using h)
theorem reducedStep_R_degree_bound (F P:Poly K) (s b:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (hP:P.degreeOf (2:Fin 4) ≤ 2 * b * (s - 1)) :
   (reducedStep F P s b).degreeOf (2:Fin 4) ≤ 2 * (b + 1) * (s - 1):=by
 let a:=2 * b * (s - 1)
 let t:=a + (2 * s - 1)
 have ht:0 < t:=by dsimp [t]; omega
 have hW:=numeratorStep_R_degree_bound F P b a s hs hF hP
 have hcoeff:liftedCoefficient (numeratorStep K F b P) t =
     excessFactor F P s b * liftedCoefficient F s:=by
   rw [numeratorStep_top_coefficient F P a s b hs hF hP]
   dsimp [excessFactor,a]
   ring
 have hks:(2 * b + 1) * (s - 1) + s = t:=by
   dsimp [t,a]
   have hsi:s = (s - 1) + 1:=by omega
   conv_lhs => rhs; rw [hsi]
   have ht':2 * s - 1 = 2 * (s - 1) + 1:=by omega
   rw [ht']
   ring
 have h:=degreeR_sub_cancel_top (numeratorStep K F b P) F (excessFactor F P s b)
   t s ((2 * b + 1) * (s - 1)) ht hW hF (excessFactor_R_degree F P s b) hks hcoeff
 have heq:t - 1 = 2 * (b + 1) * (s - 1):=by
   dsimp [t,a]
   have ht':2 * s - 1 = 2 * (s - 1) + 1:=by omega
   rw [ht',← Nat.add_assoc,Nat.add_sub_cancel]
   ring
 simpa only [reducedStep,reductionMultiplier,heq] using h
theorem reducedNumerator_R_degree_bound (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s) (b:ℕ) :
   (reducedNumerator F s b).degreeOf (2:Fin 4) ≤ 2 * b * (s - 1):=by
 induction b with
 | zero => simp [MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4) ≠ 1)]
 | succ b ih => exact reducedStep_R_degree_bound F (reducedNumerator F s b) s b hs hF ih
theorem reducedCommonNumeratorTerm_R_degree_bound (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w j:ℕ) (hj:j ≤ w) (c:ℕ → K) (x:K) :
   (reducedCommonNumeratorTerm F s w c x j).degreeOf (2:Fin 4) ≤ 2 * w * (s - 1):=by
 have hN:=reducedNumerator_R_degree_bound F s hs hF j
 have hCN:(MvPolynomial.C (c j) * reducedNumerator F s j).degreeOf (2:Fin 4) ≤
     2 * j * (s - 1) :=
   (MvPolynomial.degreeOf_C_mul_le (reducedNumerator F s j) (2:Fin 4) (c j)).trans hN
 have hH:=pderiv_same_degree_bound (2:Fin 4) F s hF
 have hHP:=degree_pow_bound (2:Fin 4) (2 * (w - j)) hH
 have hXP:((MvPolynomial.C x - MvPolynomial.X (0:Fin 4):Poly K) ^ j).degreeOf
     (2:Fin 4) ≤ 0:=by
   simpa only [Nat.mul_zero] using
     degree_pow_bound (2:Fin 4) j (shiftedX_degree_bound (2:Fin 4) (by decide) x)
 have h:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hCN hHP) hXP
 apply h.trans
 have hw:j + (w - j) = w:=by omega
 calc
   2 * j * (s - 1) + 2 * (w - j) * (s - 1) + 0 =
       2 * (j + (w - j)) * (s - 1):=by ring
   _ ≤ 2 * w * (s - 1):=by simp only [hw,le_refl]
theorem reducedClearedTaylorNumerator_R_degree_bound (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w:ℕ) (c:ℕ → K) (x:K) :
   (reducedClearedTaylorNumerator F s w c x).degreeOf (2:Fin 4) ≤ 2 * w * (s - 1):=by
 apply degree_sum_bound (2:Fin 4)
 intro j hj
 exact reducedCommonNumeratorTerm_R_degree_bound F s hs hF w j
   (by have h:=Finset.mem_range.mp hj; omega) c x
theorem reducedAgreementNumerator_R_degree_bound (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w:ℕ) (c:ℕ → K) (x u₀ u₁:K) :
   (reducedAgreementNumerator F s w c x u₀ u₁).degreeOf (2:Fin 4) ≤ 2 * w * (s - 1):=by
 apply degree_sub_bound (2:Fin 4)
 · exact reducedClearedTaylorNumerator_R_degree_bound F s hs hF w c x
 · have hA:=affineSeedPolynomial_degree_bound (2:Fin 4) 0
     (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4) ≠ 3)]) u₀ u₁
   have hH:=pderiv_same_degree_bound (2:Fin 4) F s hF
   simpa only [polyH,Nat.zero_add] using
     degree_mul_bound (2:Fin 4) hA (degree_pow_bound (2:Fin 4) (2 * w) hH)
end
end ProximityPrize.SubmissionLower.RCN262
end PackedLegacy_N8

/-! Packed from ProximityPrize.SubmissionLower.N9. -/
section PackedLegacy_N9
namespace ProximityPrize.SubmissionLower.RCN262
open scoped BigOperators
open RCN077 RCN313 RCN293 RCN261 RCN234 RCN179
noncomputable section
variable {K:Type*} [Field K]
theorem excessFactor_wt_le (weights:Fin 4 → ℕ)
   (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F P:Poly K) (s b C:ℕ) (hs:1 ≤ s)
   (hF:wt weights F ≤ C) (hP:wt weights P ≤ 1 + 2 * b * (C - 1)) :
   wt weights (excessFactor F P s b) ≤ (2 * b + 1) * (C - s):=by
 by_cases hfzero:liftedCoefficient F s = 0
 · simp [excessFactor,hfzero,wt,MvPolynomial.weightedTotalDegree]
 let f:=liftedCoefficient F s
 let c:=liftedCoefficient P (2 * b * (s - 1))
 let D:=C - s
 have hfadd:=liftedCoefficient_weight_add_le weights F s hfzero
 change wt weights f + s * weights 2 ≤ wt weights F at hfadd
 rw [hR,Nat.mul_one] at hfadd
 have hsC:s ≤ C:=by omega
 have hf:wt weights f ≤ D:=by dsimp [D]; omega
 have hc:wt weights c ≤ 1 + 2 * b * D:=by
   have h:=liftedCoefficient_weight_le_sub weights P (2 * b * (s - 1))
   change wt weights c ≤ wt weights P - 2 * b * (s - 1) * weights 2 at h
   rw [hR,Nat.mul_one] at h
   have h':=h.trans (Nat.sub_le_sub_right hP (2 * b * (s - 1)))
   have hdecomp:C - 1 = D + (s - 1):=by dsimp [D]; omega
   have heq:1 + 2 * b * (C - 1) = (1 + 2 * b * D) + 2 * b * (s - 1):=by
     rw [hdecomp]
     ring
   rwa [heq,Nat.add_sub_cancel] at h'
 have hdc:wt weights (MvPolynomial.pderiv (1:Fin 4) c) ≤ 2 * b * D:=by
   have h:=wt_pderiv_le weights c 1 (1 + 2 * b * D) hc
   rw [hY] at h
   omega
 have hdf:wt weights (MvPolynomial.pderiv (1:Fin 4) f) ≤ D - 1:=by
   simpa only [hY] using wt_pderiv_le weights f 1 D hf
 have hsf:wt weights ((s:Poly K) * f) ≤ D:=by
   have h:=wt_mul_le weights (s:Poly K) f
   rw [wt_natCast,Nat.zero_add] at h
   exact h.trans hf
 have hleft:wt weights ((s:Poly K) * f * MvPolynomial.pderiv (1:Fin 4) c) ≤
     (2 * b + 1) * D:=by
   have h:=(wt_mul_le weights ((s:Poly K) * f) (MvPolynomial.pderiv (1:Fin 4) c)).trans
     (Nat.add_le_add hsf hdc)
   apply h.trans
   apply le_of_eq
   ring
 have hright:wt weights (((2 * b * (s - 1) + 2 * b:ℕ):Poly K) *
     MvPolynomial.pderiv (1:Fin 4) f * c) ≤ (2 * b + 1) * D:=by
   by_cases hD:D = 0
   · have hz:MvPolynomial.pderiv (1:Fin 4) f = 0 :=
       pderiv_eq_zero_of_wt_lt weights f 1 (by rw [hY]; omega)
     simp [hz,wt,MvPolynomial.weightedTotalDegree]
   · have hn:wt weights (((2 * b * (s - 1) + 2 * b:ℕ):Poly K) *
         MvPolynomial.pderiv (1:Fin 4) f) ≤ D - 1:=by
       have h:=wt_mul_le weights (((2 * b * (s - 1) + 2 * b:ℕ):Poly K))
         (MvPolynomial.pderiv (1:Fin 4) f)
       rw [wt_natCast,Nat.zero_add] at h
       exact h.trans hdf
     have h:=(wt_mul_le weights
       (((2 * b * (s - 1) + 2 * b:ℕ):Poly K) * MvPolynomial.pderiv (1:Fin 4) f)
       c).trans (Nat.add_le_add hn hc)
     apply h.trans
     rw [Nat.add_mul,Nat.one_mul]
     omega
 have hinner:=(wt_sub_le weights
   ((s:Poly K) * f * MvPolynomial.pderiv (1:Fin 4) c)
   (((2 * b * (s - 1) + 2 * b:ℕ):Poly K) * MvPolynomial.pderiv (1:Fin 4) f * c)).trans
   (max_le hleft hright)
 have h:=wt_mul_le weights (s:Poly K)
   ((s:Poly K) * f * MvPolynomial.pderiv (1:Fin 4) c -
     ((2 * b * (s - 1) + 2 * b:ℕ):Poly K) * MvPolynomial.pderiv (1:Fin 4) f * c)
 rw [wt_natCast,Nat.zero_add] at h
 exact h.trans hinner
theorem reductionCorrection_wt_le (weights:Fin 4 → ℕ)
   (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F P:Poly K) (s b C:ℕ) (hs:1 ≤ s)
   (hF:wt weights F ≤ C) (hP:wt weights P ≤ 1 + 2 * b * (C - 1)) :
   wt weights (reductionMultiplier F P s b * F) ≤ 1 + 2 * (b + 1) * (C - 1):=by
 by_cases hfzero:liftedCoefficient F s = 0
 · simp [reductionMultiplier,excessFactor,hfzero,wt,MvPolynomial.weightedTotalDegree]
 have hfadd:=liftedCoefficient_weight_add_le weights F s hfzero
 change wt weights (liftedCoefficient F s) + s * weights 2 ≤ wt weights F at hfadd
 rw [hR,Nat.mul_one] at hfadd
 have hsC:s ≤ C:=by omega
 have hCpos:1 ≤ C:=hs.trans hsC
 have hq:=excessFactor_wt_le weights hY hR F P s b C hs hF hP
 have hpow:wt weights ((MvPolynomial.X (2:Fin 4):Poly K) ^ ((2 * b + 1) * (s - 1))) ≤
     (2 * b + 1) * (s - 1):=by
   have h:=wt_pow_le weights (MvPolynomial.X (2:Fin 4):Poly K) ((2 * b + 1) * (s - 1))
   simpa only [wt_X,hR,Nat.mul_one] using h
 have hqR:=(wt_mul_le weights (excessFactor F P s b)
   ((MvPolynomial.X (2:Fin 4)) ^ ((2 * b + 1) * (s - 1)))).trans
   (Nat.add_le_add hq hpow)
 have h:=(wt_mul_le weights (reductionMultiplier F P s b) F).trans
   (Nat.add_le_add hqR hF)
 apply h.trans
 have hdecomp:(C - s) + (s - 1) = C - 1:=by omega
 apply le_of_eq
 calc
   (2 * b + 1) * (C - s) + (2 * b + 1) * (s - 1) + C =
       (2 * b + 1) * ((C - s) + (s - 1)) + C:=by ring
   _ = (2 * b + 1) * (C - 1) + C:=by rw [hdecomp]
   _ = (2 * b + 1) * (C - 1) + ((C - 1) + 1) :=
     congrArg (fun n => (2 * b + 1) * (C - 1) + n) (Nat.sub_add_cancel hCpos).symm
   _ = 1 + 2 * (b + 1) * (C - 1):=by ring
theorem reducedStep_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F P:Poly K) (s b C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (hP:wt weights P ≤ 1 + 2 * b * (C - 1)) :
   wt weights (reducedStep F P s b) ≤ 1 + 2 * (b + 1) * (C - 1):=by
 have hstep:=numeratorStep_wt_le_equal_weight weights hX F P b
   (1 + 2 * b * (C - 1)) C (by omega) (by omega) (by omega) (by omega) hF hP
 rw [hR] at hstep
 have hstep':wt weights (numeratorStep K F b P) ≤ 1 + 2 * (b + 1) * (C - 1):=by
   convert hstep using 1 <;> ring
 exact (wt_sub_le weights _ _).trans
   (max_le hstep' (reductionCorrection_wt_le weights hY hR F P s b C hs hF hP))
theorem reducedNumerator_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F:Poly K) (s C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (b:ℕ) :
   wt weights (reducedNumerator F s b) ≤ 1 + 2 * b * (C - 1):=by
 induction b with
 | zero => simp only [reducedNumerator_zero,wt_X,hY,Nat.mul_zero,Nat.zero_mul,Nat.add_zero,le_refl]
 | succ b ih => exact reducedStep_wt_le weights hX hY hR F (reducedNumerator F s b) s b C hs hC hF ih
theorem reducedCommonNumeratorTerm_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F:Poly K) (s C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (w j:ℕ) (hj:j ≤ w)
   (c:ℕ → K) (x:K) :
   wt weights (reducedCommonNumeratorTerm F s w c x j) ≤ 1 + 2 * w * (C - 1):=by
 have hN:=reducedNumerator_wt_le weights hX hY hR F s C hs hC hF j
 have hCN:wt weights (MvPolynomial.C (c j) * reducedNumerator F s j) ≤
     1 + 2 * j * (C - 1):=by
   have h:=wt_mul_le weights (MvPolynomial.C (c j)) (reducedNumerator F s j)
   rw [wt_C,Nat.zero_add] at h
   exact h.trans hN
 have hH:wt weights (polyH K F) ≤ C - 1:=by
   simpa only [hR] using wt_polyH_le weights F C hF
 have hHP:=(wt_pow_le weights (polyH K F) (2 * (w - j))).trans
   (Nat.mul_le_mul_left _ hH)
 have hXP:wt weights ((MvPolynomial.C x - MvPolynomial.X (0:Fin 4):Poly K) ^ j) ≤ 0:=by
   have h:=wt_pow_le weights
     (MvPolynomial.C x - MvPolynomial.X (0:Fin 4):Poly K) j
   simpa only [shiftedX_wt_eq_zero weights hX x,Nat.mul_zero] using h
 have h1:=(wt_mul_le weights (MvPolynomial.C (c j) * reducedNumerator F s j)
   (polyH K F ^ (2 * (w - j)))).trans (Nat.add_le_add hCN hHP)
 have h2:=(wt_mul_le weights
   (MvPolynomial.C (c j) * reducedNumerator F s j * polyH K F ^ (2 * (w - j)))
   ((MvPolynomial.C x - MvPolynomial.X (0:Fin 4)) ^ j)).trans (Nat.add_le_add h1 hXP)
 apply h2.trans
 have hw:j + (w - j) = w:=by omega
 apply le_of_eq
 calc
   (1 + 2 * j * (C - 1) + 2 * (w - j) * (C - 1)) + 0 =
       1 + 2 * (j + (w - j)) * (C - 1):=by ring
   _ = 1 + 2 * w * (C - 1):=by rw [hw]
theorem reducedClearedTaylorNumerator_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F:Poly K) (s C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (w:ℕ) (c:ℕ → K) (x:K) :
   wt weights (reducedClearedTaylorNumerator F s w c x) ≤ 1 + 2 * w * (C - 1):=by
 apply wt_sum_le
 intro j hj
 exact reducedCommonNumeratorTerm_wt_le weights hX hY hR F s C hs hC hF w j
   (by have h:=Finset.mem_range.mp hj; omega) c x
theorem reducedAgreementNumerator_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F:Poly K) (s C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (w:ℕ) (c:ℕ → K) (x u₀ u₁:K) :
   wt weights (reducedAgreementNumerator F s w c x u₀ u₁) ≤
     max 1 (weights 3) + 2 * w * (C - 1):=by
 have hTaylor:=reducedClearedTaylorNumerator_wt_le weights hX hY hR F s C hs hC hF w c x
 have hA:=affineSeedPolynomial_wt_le weights u₀ u₁
 have hH:wt weights (polyH K F) ≤ C - 1:=by
   simpa only [hR] using wt_polyH_le weights F C hF
 have hHP:=(wt_pow_le weights (polyH K F) (2 * w)).trans
   (Nat.mul_le_mul_left _ hH)
 have hprod:=(wt_mul_le weights (affineSeedPolynomial u₀ u₁) (polyH K F ^ (2 * w))).trans
   (Nat.add_le_add hA hHP)
 exact (wt_sub_le weights _ _).trans (max_le
   (hTaylor.trans (Nat.add_le_add_right (Nat.le_max_left _ _) _))
   (hprod.trans (Nat.add_le_add_right (Nat.le_max_right _ _) _)))
end
end ProximityPrize.SubmissionLower.RCN262
end PackedLegacy_N9

/-! Packed from ProximityPrize.SubmissionLower.Z5. -/
section PackedLegacy_Z5
namespace ProximityPrize.SubmissionLower.RCN162
open scoped Classical
open RCN094
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def forwardResidualPoint
   (aY v bY aS bS cS:K) (q:Fin 3 → K):Fin 3 → K:=
 ![aY+v*q 0+bY*q 2,
   aS+v*q 1+bS*q 0+cS*q 2,
   q 2]
theorem eval_residualEquiv
   (aY v bY aS bS cS:K) (hv:v≠0)
   (q:Fin 3 → K) (F:Poly3 K):
   MvPolynomial.eval q
       (residualEquiv aY v bY aS bS cS hv F)=
     MvPolynomial.eval (forwardResidualPoint aY v bY aS bS cS q) F:=by
 change MvPolynomial.eval₂Hom (RingHom.id K) q
     (residualAlgHom aY v bY aS bS cS F)=
   MvPolynomial.eval₂Hom (RingHom.id K)
     (forwardResidualPoint aY v bY aS bS cS q) F
 have hq:q=![q 0,q 1,q 2]:=by
   funext i
   fin_cases i <;> rfl
 have hforward:
     forwardResidualPoint aY v bY aS bS cS q=
       ![aY+v*q 0+bY*q 2,
         aS+v*q 1+bS*q 0+cS*q 2,
         q 2]:=by
   funext i
   fin_cases i <;> simp [forwardResidualPoint]
 calc
   _=MvPolynomial.eval₂Hom (RingHom.id K) ![q 0,q 1,q 2]
         (residualAlgHom aY v bY aS bS cS F):=by rw [←hq]
   _=MvPolynomial.eval₂Hom (RingHom.id K)
         ![aY+v*q 0+bY*q 2,
           aS+v*q 1+bS*q 0+cS*q 2,
           q 2] F:=by
     simpa only [Algebra.algebraMap_self,RingHom.id_apply] using
       (eval₂Hom_residual F (q 0) (q 1) (q 2) aY v bY aS bS cS)
   _=_:=by rw [hforward]
theorem comap_pointKernel_residualEquiv
   (aY v bY aS bS cS:K) (hv:v≠0)
   (q:Fin 3 → K):
   (RingHom.ker (MvPolynomial.aeval q).toRingHom).comap
       (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom=
     RingHom.ker
       (MvPolynomial.aeval
         (forwardResidualPoint aY v bY aS bS cS q)).toRingHom:=by
 ext F
 simp only [Ideal.mem_comap,RingHom.mem_ker]
 change MvPolynomial.eval q
     (residualEquiv aY v bY aS bS cS hv F)=0 ↔
   MvPolynomial.eval (forwardResidualPoint aY v bY aS bS cS q) F=0
 rw [eval_residualEquiv]
theorem map_le_pointKernel_iff
   (aY v bY aS bS cS:K) (hv:v≠0)
   (P:Ideal (Poly3 K)) (q:Fin 3 → K):
   P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom ≤
       RingHom.ker (MvPolynomial.aeval q).toRingHom ↔
     P ≤ RingHom.ker
       (MvPolynomial.aeval
         (forwardResidualPoint aY v bY aS bS cS q)).toRingHom:=by
 rw [Ideal.map_le_iff_le_comap,
   comap_pointKernel_residualEquiv aY v bY aS bS cS hv q]
theorem map_le_pointKernel_of_forward_eq
   (aY v bY aS bS cS:K) (hv:v≠0)
   (P:Ideal (Poly3 K)) (q qOld:Fin 3 → K)
   (hforward:forwardResidualPoint aY v bY aS bS cS q=qOld)
   (hold:P ≤ RingHom.ker (MvPolynomial.aeval qOld).toRingHom):
   P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom ≤
     RingHom.ker (MvPolynomial.aeval q).toRingHom:=by
 rw [map_le_pointKernel_iff,hforward]
 exact hold
structure RegularPrimeData (G T H:Poly3 K) where
 ideal:Ideal (Poly3 K)
 isPrime:ideal.IsPrime
 G_mem:G∈ideal
 T_mem:T∈ideal
 H_not_mem:H∉ideal
 ne_point:∀ q:Fin 3 → K,
   ideal≠RingHom.ker (MvPolynomial.aeval q).toRingHom
def RegularPrimeData.mulRegularityUnit
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (c:K) (hc:c≠0):
   RegularPrimeData G T (MvPolynomial.C c*H):=by
 have hu:IsUnit (MvPolynomial.C c:Poly3 K):=
   (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
 refine {
   ideal:=D.ideal
   isPrime:=D.isPrime
   G_mem:=D.G_mem
   T_mem:=D.T_mem
   H_not_mem:=?_
   ne_point:=D.ne_point
 }
 intro hmem
 exact D.H_not_mem ((D.ideal.unit_mul_mem_iff_mem hu).mp hmem)
@[simp] theorem RegularPrimeData.mulRegularityUnit_ideal
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (c:K) (hc:c≠0):
   (D.mulRegularityUnit c hc).ideal=D.ideal:=rfl
def RegularPrimeData.mapResidual
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (aY v bY aS bS cS:K) (hv:v≠0):
   RegularPrimeData
     (residualAlgHom aY v bY aS bS cS G)
     (residualAlgHom aY v bY aS bS cS T)
     (residualAlgHom aY v bY aS bS cS H):=by
 let E:=residualEquiv aY v bY aS bS cS hv
 let Pnext:Ideal (Poly3 K):=D.ideal.map E.toRingEquiv.toRingHom
 letI:D.ideal.IsPrime:=D.isPrime
 haveI:Pnext.IsPrime:=Ideal.map_isPrime_of_equiv E.toRingEquiv
 refine {
   ideal:=Pnext
   isPrime:=inferInstance
   G_mem:=?_
   T_mem:=?_
   H_not_mem:=?_
   ne_point:=?_
 }
 · exact Ideal.mem_map_of_mem E.toRingEquiv.toRingHom D.G_mem
 · exact Ideal.mem_map_of_mem E.toRingEquiv.toRingHom D.T_mem
 · intro hmem
   exact D.H_not_mem
     ((Ideal.apply_mem_of_equiv_iff (f:=E.toRingEquiv)
       (I:=D.ideal) (x:=H)).mp hmem)
 · intro q heq
   apply D.ne_point (forwardResidualPoint aY v bY aS bS cS q)
   have hback:Pnext.comap E.toRingEquiv.toRingHom=D.ideal:=by
     ext F
     exact Ideal.apply_mem_of_equiv_iff (f:=E.toRingEquiv)
       (I:=D.ideal) (x:=F)
   rw [←hback,heq,
     comap_pointKernel_residualEquiv aY v bY aS bS cS hv q]
@[simp] theorem RegularPrimeData.mapResidual_ideal
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (aY v bY aS bS cS:K) (hv:v≠0):
   (D.mapResidual aY v bY aS bS cS hv).ideal=
     D.ideal.map
       (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom:=rfl
end
end ProximityPrize.SubmissionLower.RCN162
end PackedLegacy_Z5

/-! Packed from ProximityPrize.SubmissionLower.AE. -/
section PackedLegacy_AE
namespace ProximityPrize.SubmissionLower.RCN272
open scoped Classical BigOperators
open RCN002 RCN007 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def FiniteZeroSetBound
   (P:Ideal (MvPolynomial (Fin 3) Ω))
   (A:MvPolynomial (Fin 3) Ω) (cost:ℕ):Prop:=
 ∀ points:Finset (Fin 3 → Ω),
   (∀ v∈points,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) →
   (∀ v∈points,MvPolynomial.aeval v A=0) →
   points.card ≤ cost
structure ResidualComponentBudget
   (G T H:MvPolynomial (Fin 3) Ω)
   (Admissible:MvPolynomial (Fin 3) Ω → Prop) (wholeCost:ℕ) where
 cost:RegularComponent Ω G T H → ℕ
 zero_le:∀ (C:RegularComponent Ω G T H)
     (A:MvPolynomial (Fin 3) Ω),
   Admissible A → A∉C.1 → FiniteZeroSetBound C.1 A (cost C)
 sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCost
theorem agreement_fiber_card_le_of_zero_bound
   (P:Ideal (MvPolynomial (Fin 3) Ω))
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (Γ:Finset K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (x u₀ u₁:K) (cost:ℕ)
   (hzero:FiniteZeroSetBound P
     (agreementPolynomial φ F w x u₀ u₁) cost):
   (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤ cost:=by
 classical
 let fiber:=Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)
 let points:=fiber.image (selectedPoint φ selected)
 have hpointsP:∀ v∈points,
     P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   exact hpoint γ (Finset.mem_filter.mp hγ).1
 have hpointsA:∀ v∈points,
     MvPolynomial.aeval v (agreementPolynomial φ F w x u₀ u₁)=0:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   obtain ⟨hΓ,hagree⟩:=Finset.mem_filter.mp hγ
   exact (selected_agreement_zero_iff φ F selected p w hchar γ
     (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
 have hcount:=hzero points hpointsP hpointsA
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
 rwa [hcard] at hcount
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN272
end PackedLegacy_AE

/-! Packed from ProximityPrize.SubmissionLower.BR. -/
section PackedLegacy_BR
namespace ProximityPrize.SubmissionLower.RCN165
open scoped Classical
open RCN095 RCN094 RCN162 RCN272
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
theorem originalAlgHom_eq_residualAlgHom
   (aY v bY aS bS cS:K):
   originalAlgHom aY v bY aS bS cS=
     residualAlgHom
       (-v⁻¹*aY) v⁻¹ (-v⁻¹*bY)
       (-v⁻¹*aS+v⁻¹*bS*v⁻¹*aY)
       (-v⁻¹*bS*v⁻¹)
       (v⁻¹*bS*v⁻¹*bY-v⁻¹*cS):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [originalAlgHom,residualAlgHom,originalImage,residualImage] <;>
   ring
theorem polynomialInFlag_originalAlgHom
   (r:FlagDegree) (A:Poly3 K) (aY v bY aS bS cS:K)
   (hA:PolynomialInFlag r A):
   PolynomialInFlag r (originalAlgHom aY v bY aS bS cS A):=by
 rw [originalAlgHom_eq_residualAlgHom]
 exact RCN094.polynomialInFlag_residualAlgHom
   r A _ _ _ _ _ _ hA
@[simp] theorem residual_original_apply
   (aY v bY aS bS cS:K) (hv:v≠0) (A:Poly3 K):
   residualAlgHom aY v bY aS bS cS
       (originalAlgHom aY v bY aS bS cS A)=A:=by
 have h:=AlgHom.congr_fun
   (residual_comp_original aY v bY aS bS cS hv) A
 simpa only [AlgHom.comp_apply,AlgHom.id_apply] using h
theorem forwardResidualPoint_injective
   (aY v bY aS bS cS:K) (hv:v≠0):
   Function.Injective (forwardResidualPoint aY v bY aS bS cS):=by
 intro q r hqr
 have h0:=congrFun hqr 0
 have h1:=congrFun hqr 1
 have h2:=congrFun hqr 2
 simp only [forwardResidualPoint,Matrix.cons_val_zero,
   Matrix.cons_val_one,Matrix.cons_val_two] at h0 h1 h2
 change q 2=r 2 at h2
 have hy:q 0=r 0:=by
   apply (mul_left_cancel₀ hv)
   rw [h2] at h0
   linear_combination h0
 have hs:q 1=r 1:=by
   apply (mul_left_cancel₀ hv)
   rw [hy,h2] at h1
   linear_combination h1
 funext i
 fin_cases i
 · exact hy
 · exact hs
 · exact h2
theorem finiteZeroSetBound_map_residual
   (aY v bY aS bS cS:K) (hv:v≠0)
   (P:Ideal (Poly3 K)) (A:Poly3 K) (cost:ℕ)
   (hzero:FiniteZeroSetBound P A cost):
   FiniteZeroSetBound
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     (residualAlgHom aY v bY aS bS cS A) cost:=by
 classical
 intro points hpointsP hpointsA
 let forward:=forwardResidualPoint aY v bY aS bS cS
 let oldPoints:=points.image forward
 have hcard:oldPoints.card=points.card:=by
   exact Finset.card_image_of_injective points
     (forwardResidualPoint_injective aY v bY aS bS cS hv)
 rw [←hcard]
 apply hzero oldPoints
 · intro qOld hqOld
   obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hqOld
   exact (map_le_pointKernel_iff aY v bY aS bS cS hv P q).mp
     (hpointsP q hq)
 · intro qOld hqOld
   obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hqOld
   have hz:=hpointsA q hq
   change MvPolynomial.eval q
     (residualAlgHom aY v bY aS bS cS A)=0 at hz
   change MvPolynomial.eval
     (forwardResidualPoint aY v bY aS bS cS q) A=0
   change MvPolynomial.eval q
     (residualEquiv aY v bY aS bS cS hv A)=0 at hz
   rwa [eval_residualEquiv] at hz
theorem finiteZeroSetBound_map_residual_of_inverse
   (aY v bY aS bS cS:K) (hv:v≠0)
   (P:Ideal (Poly3 K)) (A:Poly3 K) (cost:ℕ)
   (hzero:FiniteZeroSetBound P
     (originalAlgHom aY v bY aS bS cS A) cost):
   FiniteZeroSetBound
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     A cost:=by
 have h:=finiteZeroSetBound_map_residual aY v bY aS bS cS hv P
   (originalAlgHom aY v bY aS bS cS A) cost hzero
 change FiniteZeroSetBound
   (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
   (residualAlgHom aY v bY aS bS cS
     (originalAlgHom aY v bY aS bS cS A)) cost at h
 rw [residual_original_apply aY v bY aS bS cS hv] at h
 exact h
structure PrimeFlagZeroBudget
   (P:Ideal (Poly3 K)) (cost:FlagDegree → ℕ) where
 zero_le:∀ (r:FlagDegree) (A:Poly3 K),
   PolynomialInFlag r A → A∉P → FiniteZeroSetBound P A (cost r)
def PrimeFlagZeroBudget.mapResidual
   {P:Ideal (Poly3 K)} {cost:FlagDegree → ℕ}
   (B:PrimeFlagZeroBudget P cost)
   (aY v bY aS bS cS:K) (hv:v≠0):
   PrimeFlagZeroBudget
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     cost where
 zero_le:=by
   intro r A hA hproper
   have hAold:PolynomialInFlag r
       (originalAlgHom aY v bY aS bS cS A):=
     polynomialInFlag_originalAlgHom r A aY v bY aS bS cS hA
   have hproperOld:originalAlgHom aY v bY aS bS cS A∉P:=by
     intro hmem
     apply hproper
     have hmapped:=Ideal.mem_map_of_mem
       (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom hmem
     change residualAlgHom aY v bY aS bS cS
       (originalAlgHom aY v bY aS bS cS A)∈
         P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom
       at hmapped
     rwa [residual_original_apply aY v bY aS bS cS hv] at hmapped
   exact finiteZeroSetBound_map_residual_of_inverse
     aY v bY aS bS cS hv P A (cost r)
     (B.zero_le r _ hAold hproperOld)
end
end ProximityPrize.SubmissionLower.RCN165
end PackedLegacy_BR

/-! Packed from ProximityPrize.SubmissionLower.BE. -/
section PackedLegacy_BE
namespace ProximityPrize.SubmissionLower.RCN123
open scoped Classical
open RCN095 RCN125 RCN371 RCN011
 RCN009 RCN012
noncomputable section
variable {K:Type} [Field K]
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
structure FlagTrapezoidCaps (p:FlagDegree) (F:Poly3 K):Prop where
 uOuter:(planeMap K uOrder F).natDegree ≤ p.all
 uTotal:∀ d∈(rationalMap K uOrder F).support,
   d 0+d 1 ≤ p.zOnly+p.yz+p.all
 vOuter:(planeMap K vOrder F).natDegree ≤ p.yz+p.all
 vTotal:∀ d∈(rationalMap K vOrder F).support,
   d 0+d 1 ≤ p.zOnly+p.yz+p.all
 zOuter:(planeMap K zOrder F).natDegree ≤ p.all
 zTotal:∀ d∈(rationalMap K zOrder F).support,
   d 0+d 1 ≤ p.yz+p.all
private theorem degreeOf_s_le
   {p:FlagDegree} {F:Poly3 K}
   (hF:RCN125.PolynomialInFlag p F):
   F.degreeOf 1 ≤ p.all:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 exact (hF d hd).1
private theorem degreeOf_y_le
   {p:FlagDegree} {F:Poly3 K}
   (hF:RCN125.PolynomialInFlag p F):
   F.degreeOf 0 ≤ p.yz+p.all:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 exact (Nat.le_add_right (d 0) (d 1)).trans (hF d hd).2.1
theorem flagTrapezoidCaps_of_inFlag
   (p:FlagDegree) (F:Poly3 K)
   (hF:RCN125.PolynomialInFlag p F):
   FlagTrapezoidCaps p F:=by
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · exact (planeMap_natDegree_le K uOrder F).trans
     (by simpa [uOrder] using degreeOf_s_le hF)
 · apply rationalMap_joint_support_of_original K uOrder F _
   intro d hd
   have h:=(hF d hd).2.2
   have h':d 1+d 2 ≤ p.zOnly+p.yz+p.all:=by omega
   simpa [uOrder] using h'
 · exact (planeMap_natDegree_le K vOrder F).trans
     (by simpa [vOrder,Equiv.swap_apply_def] using degreeOf_y_le hF)
 · apply rationalMap_joint_support_of_original K vOrder F _
   intro d hd
   have h:=(hF d hd).2.2
   have h':d 0+d 2 ≤ p.zOnly+p.yz+p.all:=by omega
   simpa [vOrder,Equiv.swap_apply_def] using h'
 · exact (planeMap_natDegree_le K zOrder F).trans
     (by simpa [zOrder,Equiv.swap_apply_def] using degreeOf_s_le hF)
 · apply rationalMap_joint_support_of_original K zOrder F _
   intro d hd
   have h:=(hF d hd).2.1
   simpa [zOrder,Equiv.swap_apply_def,Nat.add_comm] using h
theorem flagTrapezoidCaps_flagAlgHom
   (p:FlagDegree) (F:Poly3 K) (lam mu nu:K)
   (hF:F.support ⊆ flagSupport p):
   FlagTrapezoidCaps p (flagAlgHom lam mu nu F):=by
 apply flagTrapezoidCaps_of_inFlag
 apply polynomialInFlag_flagAlgHom p F lam mu nu
 intro d hd
 exact (mem_flagSupport_iff p d).mp (hF hd)
theorem u_trapezoid_budget6543 (m:ℕ) (hm:m ≤ 1179639):
   m*376+5*98434322-m*5 ≤ flagYZMixedCap:=by
 rw [flag_mixed_values.2.2.1]
 omega
theorem v_trapezoid_budget6543 (m:ℕ) (hm:m ≤ 6684622):
   m*376+26*98434322-m*26 ≤ flagAllMixedCap:=by
 rw [flag_mixed_values.2.2.2]
 omega
theorem z_trapezoid_budget6543 (m:ℕ) (hm:m ≤ 1179639):
   m*26+5*6684622-m*5 ≤ flagZMixedCap:=by
 rw [flag_mixed_values.2.1]
 omega
end
end ProximityPrize.SubmissionLower.RCN123
end PackedLegacy_BE

/-! Packed from ProximityPrize.SubmissionLower.Z2. -/
section PackedLegacy_Z2
namespace ProximityPrize.SubmissionLower.RCN121
open RCN095
theorem flagMixed_projection_decomposition
   (p q r:FlagDegree):
   flagMixed p q r=
     r.zOnly*flagMixed p q unitZFlag+
     r.yz*flagMixed p q unitYZFlag+
     r.all*flagMixed p q unitAllFlag:=by
 cases p
 cases q
 cases r
 simp [flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
 ring
theorem trapezoid_budget_mono
   (n mCap totalG totalT m:ℕ)
   (hn:n ≤ totalG) (hm:m ≤ mCap):
   m*totalG+n*totalT-m*n ≤
     mCap*totalG+n*totalT-mCap*n:=by
 let delta:=totalG-n
 have hsplit:totalG=n+delta:=by
   dsimp only [delta]
   omega
 have hdecomp (a:ℕ):
     a*totalG=a*n+a*delta:=by
   rw [hsplit,Nat.mul_add]
 have hdelta:m*delta ≤ mCap*delta:=
   Nat.mul_le_mul_right delta hm
 rw [hdecomp m,hdecomp mCap]
 omega
theorem u_flag_trapezoid_budget
   (p q:FlagDegree) (m:ℕ) (hm:m ≤ q.all):
   m*(p.zOnly+p.yz+p.all)+
         p.all*(q.zOnly+q.yz+q.all)-m*p.all ≤
     flagMixed p q unitYZFlag:=by
 calc
   m*(p.zOnly+p.yz+p.all)+
         p.all*(q.zOnly+q.yz+q.all)-m*p.all ≤
       q.all*(p.zOnly+p.yz+p.all)+
         p.all*(q.zOnly+q.yz+q.all)-q.all*p.all:=
     trapezoid_budget_mono p.all q.all
       (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all) m
       (by omega) hm
   _=flagMixed p q unitYZFlag:=by
     have hsum:
         q.all*(p.zOnly+p.yz+p.all)+
             p.all*(q.zOnly+q.yz+q.all)=
           q.all*p.all+flagMixed p q unitYZFlag:=by
       simp [flagMixed,unitYZFlag]
       ring
     rw [hsum,Nat.add_sub_cancel_left]
theorem v_flag_trapezoid_budget
   (p q:FlagDegree) (m:ℕ) (hm:m ≤ q.yz+q.all):
   m*(p.zOnly+p.yz+p.all)+
         (p.yz+p.all)*(q.zOnly+q.yz+q.all)-
           m*(p.yz+p.all) ≤
     flagMixed p q unitAllFlag:=by
 calc
   m*(p.zOnly+p.yz+p.all)+
         (p.yz+p.all)*(q.zOnly+q.yz+q.all)-
           m*(p.yz+p.all) ≤
       (q.yz+q.all)*(p.zOnly+p.yz+p.all)+
         (p.yz+p.all)*(q.zOnly+q.yz+q.all)-
           (q.yz+q.all)*(p.yz+p.all):=
     trapezoid_budget_mono (p.yz+p.all) (q.yz+q.all)
       (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all) m
       (by omega) hm
   _=flagMixed p q unitAllFlag:=by
     have hsum:
         (q.yz+q.all)*(p.zOnly+p.yz+p.all)+
             (p.yz+p.all)*(q.zOnly+q.yz+q.all)=
           (q.yz+q.all)*(p.yz+p.all)+
             flagMixed p q unitAllFlag:=by
       simp [flagMixed,unitAllFlag]
       ring
     rw [hsum,Nat.add_sub_cancel_left]
end ProximityPrize.SubmissionLower.RCN121
end PackedLegacy_Z2
end Compact_PackedLegacyCore2
