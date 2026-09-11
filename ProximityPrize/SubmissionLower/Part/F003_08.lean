import ProximityPrize.SubmissionLower.Part.F003_07
section Compact_PackedLegacyCore1
section PackedLegacy_C1
namespace ProximityPrize.SubmissionLower.RCN100
open RCN119 ProximityPrize.Benchmark
open scoped BigOperators
noncomputable section
variable (K:Type*) [Field K]

theorem all_blocks_divisible_of_equations
   (D w L s m:ℕ) (x u₀ u₁:K)
   (θ:CoefficientIndex D w L s → K)
   (h:∀ r:Fin m,contactJet K (m-r.val)
     ((extractBlock K D w L s x u₀ u₁ r.val θ):Poly K)=0):
   ∀ r:ℕ,slopeDifference K^(m-r)∣
     ((extractBlock K D w L s x u₀ u₁ r θ):Poly K):=by
 intro r
 by_cases hr:r < m
 · exact (contactJet_eq_zero_iff K (m-r) _).mp (h ⟨r,hr⟩)
 · have hm:m-r=0:=by omega
   simp only [hm,pow_zero,one_dvd]
end
end ProximityPrize.SubmissionLower.RCN100
end PackedLegacy_C1

/-! Packed from ProximityPrize.SubmissionLower.BD. -/
section PackedLegacy_BD
namespace ProximityPrize.SubmissionLower.RCN122
open RCN119 RCN100 ProximityPrize.Benchmark
open scoped BigOperators
noncomputable section
variable (K:Type*) [Field K]
abbrev LocalPolynomial:=Polynomial (Poly K)
def translationVariables (x u₀ u₁:K):Fin 4 → LocalPolynomial K:=
 ![Polynomial.X+Polynomial.C (MvPolynomial.C x),
   Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
     Polynomial.C (seedAffine K u₀ u₁),
   Polynomial.C (MvPolynomial.X 1),
   Polynomial.C (MvPolynomial.X 2)]
def homogenizedTranslation (x u₀ u₁:K):
   MvPolynomial (Fin 4) K →ₐ[K] LocalPolynomial K:=
 MvPolynomial.aeval (translationVariables K x u₀ u₁)
theorem columnMonomial_eq (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a=
     MvPolynomial.C a*MvPolynomial.X 0^c.2.2.2.val*
       MvPolynomial.X 1^c.1.val*MvPolynomial.X 2^c.2.1.val*
       MvPolynomial.X 3^c.2.2.1.val:=by
 rw [columnExponent,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
   ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem localMonomial_eq (f j z:ℕ):
   localMonomial K f j z=
     MvPolynomial.X 0^f*MvPolynomial.X 1^j*MvPolynomial.X 2^z:=by
 rw [localMonomial,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single, ←MvPolynomial.X_pow_eq_monomial]
theorem coeff_shifted_affine_product
   {A:Type*} [CommRing A] (x a y b:A) (e i r:ℕ):
   (((Polynomial.X+Polynomial.C x)^e*
       (Polynomial.X*Polynomial.C y+Polynomial.C a)^i*
       Polynomial.C b):Polynomial A).coeff r=
     ∑ f:Fin (i+1),if f.val ≤ r then
       (x^(e-(r-f.val))*(e.choose (r-f.val):A))*
         (y^f.val*a^(i-f.val)*(i.choose f.val:A)*b)
     else 0:=by
 rw [add_pow (Polynomial.X*Polynomial.C y) (Polynomial.C a) i,
   Finset.mul_sum,Finset.sum_mul,Polynomial.finsetSum_coeff]
 rw [Finset.sum_range]
 apply Finset.sum_congr rfl
 intro f hf
 have hfactor:
     (((Polynomial.X+Polynomial.C x)^e*
       ((Polynomial.X*Polynomial.C y)^f.val*
         Polynomial.C a^(i-f.val)*(i.choose f.val:Polynomial A)))*
         Polynomial.C b)=
       (((Polynomial.X+Polynomial.C x)^e*
         Polynomial.C (y^f.val*a^(i-f.val)*(i.choose f.val:A)*b))*
         Polynomial.X^f.val):=by
   simp only [mul_pow,map_mul,map_pow,map_natCast]
   ring
 rw [hfactor,Polynomial.coeff_mul_X_pow']
 split_ifs with hfr
 · rw [Polynomial.coeff_mul_C,Polynomial.coeff_X_add_C_pow]
 · rfl
theorem translation_column (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (a:K):
   homogenizedTranslation K x u₀ u₁ (MvPolynomial.monomial (columnExponent c) a)=
     Polynomial.C (MvPolynomial.C a)*
       (Polynomial.X+Polynomial.C (MvPolynomial.C x))^c.2.2.2.val*
       (Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
         Polynomial.C (seedAffine K u₀ u₁))^c.1.val*
       Polynomial.C (MvPolynomial.X 1)^c.2.1.val*
       Polynomial.C (MvPolynomial.X 2)^c.2.2.1.val:=by
 rw [columnMonomial_eq K D w L s c a]
 simp [homogenizedTranslation,translationVariables,
   Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq]
theorem translation_column_coeff (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (a:K) (r:ℕ):
   (homogenizedTranslation K x u₀ u₁
     (MvPolynomial.monomial (columnExponent c) a)).coeff r=
       a • blockEntry K D w L s x u₀ u₁ c r:=by
 have hfactor:
     homogenizedTranslation K x u₀ u₁
       (MvPolynomial.monomial (columnExponent c) a)=
     Polynomial.C (MvPolynomial.C a)*
       ((Polynomial.X+Polynomial.C (MvPolynomial.C x))^c.2.2.2.val*
         (Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
           Polynomial.C (seedAffine K u₀ u₁))^c.1.val*
         Polynomial.C (MvPolynomial.X 1^c.2.1.val*
           MvPolynomial.X 2^c.2.2.1.val)):=by
   rw [translation_column K D w L s x u₀ u₁ c a]
   simp only [map_mul,map_pow]
   ring
 rw [hfactor,Polynomial.coeff_C_mul,coeff_shifted_affine_product]
 unfold blockEntry
 rw [Finset.mul_sum,Finset.smul_sum]
 apply Finset.sum_congr rfl
 intro f hf
 split_ifs with hfr
 · simp only [localMonomial_eq,MvPolynomial.smul_eq_C_mul,
     map_mul,map_pow,map_natCast]
   ring
 · simp
theorem translation_reconstruct_coeff (D w L s:ℕ) (x u₀ u₁:K)
   (θ:CoefficientIndex D w L s → K) (r:ℕ):
   (homogenizedTranslation K x u₀ u₁ (reconstruct K D w L s θ)).coeff r=
     ((extractBlock K D w L s x u₀ u₁ r θ):Poly K):=by
 rw [reconstruct,map_sum,Polynomial.finsetSum_coeff]
 simp only [translation_column_coeff]
 change (∑ c:CoefficientIndex D w L s,
   θ c • blockEntry K D w L s x u₀ u₁ c r)=
     (((∑ c:CoefficientIndex D w L s,
       θ c • boundedBlockEntry K D w L s x u₀ u₁ c r):
         coefficientBox K (min r L) L s):Poly K)
 simp [boundedBlockEntry]
def contactEvaluation (R B:Polynomial K) (γ:K):Poly K →ₐ[K] Polynomial K:=
 MvPolynomial.aeval ![R+Polynomial.X*B,R,Polynomial.C γ]
def outerEvaluation (R B:Polynomial K) (γ:K):
   LocalPolynomial K →+*Polynomial K:=
 Polynomial.eval₂RingHom (contactEvaluation K R B γ).toRingHom Polynomial.X
@[simp] theorem contactEvaluation_slopeDifference (R B:Polynomial K) (γ:K):
   contactEvaluation K R B γ (slopeDifference K)=Polynomial.X*B:=by
 simp [contactEvaluation,slopeDifference]
theorem contactEvaluation_seedAffine (R B:Polynomial K) (γ u₀ u₁:K):
   contactEvaluation K R B γ (seedAffine K u₀ u₁)=
     Polynomial.C (u₀+γ*u₁):=by
 rw [seedAffine, ←MvPolynomial.C_mul_X_eq_monomial]
 simp [contactEvaluation,Polynomial.algebraMap_eq,mul_comm]
theorem outerEvaluation_contact_dvd
   (H:LocalPolynomial K) (m:ℕ) (R B:Polynomial K) (γ:K)
   (hcoeff:∀ r:ℕ,slopeDifference K^(m-r)∣H.coeff r):
   (Polynomial.X:Polynomial K)^m∣outerEvaluation K R B γ H:=by
 classical
 change (Polynomial.X:Polynomial K)^m∣
   H.eval₂ (contactEvaluation K R B γ).toRingHom Polynomial.X
 rw [Polynomial.eval₂_eq_sum]
 change (Polynomial.X:Polynomial K)^m∣
   ∑ r∈H.support,contactEvaluation K R B γ (H.coeff r)*Polynomial.X^r
 apply Finset.dvd_sum
 intro r hr
 have hlocal:(Polynomial.X:Polynomial K)^(m-r)∣
     contactEvaluation K R B γ (H.coeff r):=by
   obtain ⟨q,hq⟩:=hcoeff r
   refine ⟨B^(m-r)*contactEvaluation K R B γ q,?_⟩
   simp only [hq,map_mul,map_pow,contactEvaluation_slopeDifference,
     mul_pow,mul_assoc]
 have hprod:=mul_dvd_mul hlocal
   (dvd_refl ((Polynomial.X:Polynomial K)^r))
 have htotal:(Polynomial.X:Polynomial K)^((m-r)+r)∣
     contactEvaluation K R B γ (H.coeff r)*Polynomial.X^r:=by
   simpa only [pow_add] using hprod
 exact (pow_dvd_pow Polynomial.X (show m ≤ (m-r)+r by omega)).trans htotal
def specialization (P:Polynomial K) (γ:K):
   MvPolynomial (Fin 4) K →ₐ[K] Polynomial K:=
 MvPolynomial.aeval ![Polynomial.X,P,P.derivative,Polynomial.C γ]
theorem outerEvaluation_translation
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K)
   (x u₀ u₁ γ:K) (B:Polynomial K)
   (hP:Polynomial.taylor x P=
     Polynomial.C (u₀+γ*u₁)+Polynomial.X*
       (Polynomial.taylor x P.derivative+Polynomial.X*B)):
   outerEvaluation K (Polynomial.taylor x P.derivative) B γ
       (homogenizedTranslation K x u₀ u₁ Q)=
     Polynomial.taylor x (specialization K P γ Q):=by
 have hhom:
     (outerEvaluation K (Polynomial.taylor x P.derivative) B γ).comp
       (homogenizedTranslation K x u₀ u₁).toRingHom=
     (Polynomial.taylorAlgHom x).toRingHom.comp
       (specialization K P γ).toRingHom:=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,outerEvaluation,contactEvaluation,
       homogenizedTranslation,specialization,Polynomial.algebraMap_apply,
       MvPolynomial.algebraMap_eq]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,outerEvaluation,contactEvaluation,
         homogenizedTranslation,translationVariables,specialization,
         seedAffine,MvPolynomial.aeval_monomial,Polynomial.algebraMap_apply,
         MvPolynomial.algebraMap_eq,hP] <;> ring
 exact DFunLike.congr_fun hhom Q
theorem X_pow_dvd_taylor_specialization
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K)
   (x u₀ u₁ γ:K) (m:ℕ)
   (hvalue:P.eval x=u₀+γ*u₁)
   (hcoeff:∀ r:ℕ,slopeDifference K^(m-r)∣
     (homogenizedTranslation K x u₀ u₁ Q).coeff r):
   (Polynomial.X:Polynomial K)^m∣
     Polynomial.taylor x (specialization K P γ Q):=by
 obtain ⟨B,hB⟩:=RCN185.X_sq_dvd_contactResidual P x
 have hP:Polynomial.taylor x P=
     Polynomial.C (u₀+γ*u₁)+Polynomial.X*
       (Polynomial.taylor x P.derivative+Polynomial.X*B):=by
   change Polynomial.taylor x P-Polynomial.C (P.eval x)-
     Polynomial.X*Polynomial.taylor x P.derivative=Polynomial.X^2*B at hB
   rw [hvalue] at hB
   linear_combination hB
 have hh:=outerEvaluation_contact_dvd K
   (homogenizedTranslation K x u₀ u₁ Q) m (Polynomial.taylor x P.derivative) B γ hcoeff
 rw [outerEvaluation_translation K Q P x u₀ u₁ γ B hP] at hh
 exact hh
theorem specialization_eq_zero_of_contact_and_degree
   [DecidableEq K] {I:Type*} [DecidableEq I]
   (Q:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K)
   (nodes:I ↪ K) (u₀ u₁:I → K) (support:Finset I) (m:ℕ)
   (hcontact:∀ i∈support,∀ r:ℕ,slopeDifference K^(m-r)∣
     (homogenizedTranslation K (nodes i) (u₀ i) (u₁ i) Q).coeff r)
   (hvalues:∀ i∈support,P.eval (nodes i)=u₀ i+γ*u₁ i)
   (hdegree:(specialization K P γ Q).natDegree < m*support.card):
   specialization K P γ Q=0:=by
 by_contra hnonzero
 have hmult:∀ i∈support,
     m ≤ (specialization K P γ Q).rootMultiplicity (nodes i):=by
   intro i hi
   have hlocal:=X_pow_dvd_taylor_specialization K Q P
     (nodes i) (u₀ i) (u₁ i) γ m (hvalues i hi) (hcontact i hi)
   have hshifted:(Polynomial.X-Polynomial.C (nodes i))^m∣
       specialization K P γ Q:=
     (RCN185.shifted_power_dvd_iff_taylor_coeff_zero
       (specialization K P γ Q) (nodes i) m).mpr (Polynomial.X_pow_dvd_iff.mp hlocal)
   exact (Polynomial.le_rootMultiplicity_iff hnonzero).mpr hshifted
 have hh:=BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
   (specialization K P γ Q) nodes support m hmult
 exact (Nat.not_le_of_gt hdegree) hh
theorem monomial_eq (d:Fin 4 →₀ ℕ) (a:K):
   MvPolynomial.monomial d a=
     MvPolynomial.C a*MvPolynomial.X 0^d 0*MvPolynomial.X 1^d 1*
       MvPolynomial.X 2^d 2*MvPolynomial.X 3^d 3:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3):=by
   ext i
   fin_cases i <;> simp
 conv_lhs => rw [hd]
 rw [MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single, ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem specialization_monomial
   (P:Polynomial K) (γ:K) (d:Fin 4 →₀ ℕ) (a:K):
   specialization K P γ (MvPolynomial.monomial d a)=
     Polynomial.C a*Polynomial.X^d 0*P^d 1*P.derivative^d 2*
       Polynomial.C γ^d 3:=by
 rw [monomial_eq K d a]
 simp [specialization,Polynomial.algebraMap_eq]
theorem specialization_monomial_natDegree_le
   (P:Polynomial K) (γ:K) (w:ℕ) (hP:P.natDegree ≤ w)
   (d:Fin 4 →₀ ℕ) (a:K):
   (specialization K P γ (MvPolynomial.monomial d a)).natDegree ≤
     d 0+w*d 1+(w-1)*d 2:=by
 rw [specialization_monomial]
 have hc:(Polynomial.C a:Polynomial K).natDegree ≤ 0:=by simp
 have hx:((Polynomial.X:Polynomial K)^d 0).natDegree ≤ d 0:=by simp
 have hy:(P^d 1).natDegree ≤ d 1*w:=
   Polynomial.natDegree_pow_le_of_le (d 1) hP
 have hderiv:P.derivative.natDegree ≤ w-1:=
   (Polynomial.natDegree_derivative_le P).trans (Nat.sub_le_sub_right hP 1)
 have hr:(P.derivative^d 2).natDegree ≤ d 2*(w-1):=
   Polynomial.natDegree_pow_le_of_le (d 2) hderiv
 have hz:((Polynomial.C γ:Polynomial K)^d 3).natDegree ≤ 0:=by
   simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 3)
     (show (Polynomial.C γ:Polynomial K).natDegree ≤ 0 by simp)
 have hh:=Polynomial.natDegree_mul_le_of_le
   (Polynomial.natDegree_mul_le_of_le
     (Polynomial.natDegree_mul_le_of_le
       (Polynomial.natDegree_mul_le_of_le hc hx) hy) hr) hz
 simpa only [Nat.zero_add,Nat.add_zero,Nat.mul_comm] using hh
theorem specialization_natDegree_lt
   (D w L s:ℕ) (Q:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K)
   (hD:0 < D) (hcaps:Q∈globalCoefficientBox K D w L s)
   (hP:P.natDegree ≤ w):
   (specialization K P γ Q).natDegree < D:=by
 classical
 have hsupport:∀ d∈Q.support,
     d 1+d 2+d 3 ≤ L∧d 2 ≤ s∧
       d 0+w*d 1+(w-1)*d 2 < D:=hcaps
 have hterms:∀ d∈Q.support,
     (specialization K P γ (MvPolynomial.monomial d (MvPolynomial.coeff d Q))).natDegree ≤
       D-1:=by
   intro d hd
   have hweight:=(hsupport d hd).2.2
   have hh:=specialization_monomial_natDegree_le K P γ w hP d (MvPolynomial.coeff d Q)
   omega
 rw [MvPolynomial.as_sum Q,map_sum]
 have hh:=Polynomial.natDegree_sum_le_of_forall_le Q.support
   (fun d => specialization K P γ (MvPolynomial.monomial d (MvPolynomial.coeff d Q))) hterms
 exact lt_of_le_of_lt hh (by omega)
end
end ProximityPrize.SubmissionLower.RCN122
end PackedLegacy_BD

/-! Packed from ProximityPrize.SubmissionLower.C2. -/
section PackedLegacy_C2
namespace ProximityPrize.SubmissionLower.RCN101
open ProximityPrize.Benchmark RCN100 RCN119 RCN122
noncomputable section
variable (K:Type*) [Field K]
theorem block_equations_of_mem_ker
   {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1)):
   ∀ (i:I) (r:Fin m),
     contactJet K (m-r.val)
       ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val theta):
         Poly K)=0:=by
 intro i r
 have hzero:constraintMap K D w L s m nodes u0 u1 theta=0:=
   LinearMap.mem_ker.mp htheta
 have happ:=congrArg
   (fun target:GlobalTarget K I m L s => ((target i r):Poly K)) hzero
 change contactJet K (m-r.val)
   ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val theta):
     Poly K)=0 at happ
 exact happ
theorem translated_contact_of_mem_ker
   {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1)):
   ∀ (i:I) (r:ℕ),
     slopeDifference K^(m-r)∣
       (homogenizedTranslation K (nodes i) (u0 i) (u1 i)
         (reconstruct K D w L s theta)).coeff r:=by
 intro i r
 rw [translation_reconstruct_coeff]
 exact all_blocks_divisible_of_equations K D w L s m
   (nodes i) (u0 i) (u1 i) theta
   (block_equations_of_mem_ker K D w L s m nodes u0 u1 theta htheta i) r
theorem specialization_eq_zero_of_mem_ker
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (P:Polynomial K) (gamma:K) (support:Finset I)
   (hD:0 < D) (hP:P.natDegree ≤ w)
   (hcapacity:D ≤ m*support.card)
   (hvalues:∀ i∈support,
     P.eval (nodes i)=u0 i+gamma*u1 i):
   specialization K P gamma (reconstruct K D w L s theta)=0:=by
 apply specialization_eq_zero_of_contact_and_degree K
   (reconstruct K D w L s theta) P gamma nodes u0 u1 support m
 · intro i hi r
   exact translated_contact_of_mem_ker K D w L s m nodes u0 u1 theta
     htheta i r
 · exact hvalues
 · have hdegree:=specialization_natDegree_lt K D w L s
     (reconstruct K D w L s theta) P gamma hD
     (reconstruct_mem_globalCoefficientBox K D w L s theta) hP
   exact hdegree.trans_le hcapacity
theorem specialization_eq_zero_of_agreements
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m a:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (hD:0 < D) (hDa:D=m*a)
   (P:Polynomial K) (gamma:K) (support:Finset I)
   (hP:P.natDegree ≤ w) (hcard:a ≤ support.card)
   (hvalues:∀ i∈support,
     P.eval (nodes i)=u0 i+gamma*u1 i):
   specialization K P gamma (reconstruct K D w L s theta)=0:=by
 apply specialization_eq_zero_of_mem_ker K D w L s m nodes u0 u1 theta
   htheta P gamma support hD hP
 · rw [hDa]
   exact Nat.mul_le_mul_left m hcard
 · exact hvalues
theorem nonzero_kernel_member_universal
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m a:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta0:theta≠0)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (hD:0 < D) (hDa:D=m*a):
   reconstruct K D w L s theta≠0∧
     reconstruct K D w L s theta∈globalCoefficientBox K D w L s∧
     ∀ (gamma:K) (P:Polynomial K) (support:Finset I),
       P.natDegree ≤ w → a ≤ support.card →
       (∀ i∈support,
         P.eval (nodes i)=u0 i+gamma*u1 i) →
       specialization K P gamma (reconstruct K D w L s theta)=0:=by
 refine ⟨reconstruct_ne_zero K D w L s theta htheta0,
   reconstruct_mem_globalCoefficientBox K D w L s theta,?_⟩
 intro gamma P support hP hcard hvalues
 exact specialization_eq_zero_of_agreements K D w L s m a nodes u0 u1
   theta htheta hD hDa P gamma support hP hcard hvalues
theorem flag_box_to_ordinary (D w L s:ℕ)
   (Q:MvPolynomial (Fin 4) K)
   (hQ:Q∈globalCoefficientBox K D w L s):
   Q∈RCN174.globalCoefficientBox K D w L s:=by
 intro d hd
 obtain ⟨hT,hR,hD⟩:=hQ hd
 exact ⟨by omega,hR,hD⟩
theorem specialization_eq_ordinary (P:Polynomial K) (gamma:K):
   specialization K P gamma=RCN319.specialization K P gamma:=rfl
end
end ProximityPrize.SubmissionLower.RCN101
end PackedLegacy_C2

/-! Packed from ProximityPrize.SubmissionLower.I4. -/
section PackedLegacy_I4
namespace ProximityPrize.SubmissionLower.RCN071
open scoped BigOperators
open RCN081
noncomputable section
variable {K:Type*} [Field K]
theorem weightedTotalDegree_prod_eq
   {I:Type*} [DecidableEq I] (weights:Fin 4 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 4) K)
   (hf:∀ i∈s,f i≠0):
   MvPolynomial.weightedTotalDegree weights (∏ i∈s,f i)=
     ∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i):=by
 classical
 induction s using Finset.induction_on with
 | empty => simp [MvPolynomial.weightedTotalDegree]
 | @insert a s ha ih =>
     have hfa:f a≠0:=hf a (Finset.mem_insert_self a s)
     have hfs:∀ i∈s,f i≠0:=
       fun i hi↦hf i (Finset.mem_insert_of_mem hi)
     have hprod:∏ i∈s,f i≠0:=
       Finset.prod_ne_zero_iff.mpr hfs
     rw [Finset.prod_insert ha,Finset.sum_insert ha,
       weightedTotalDegree_mul weights (f a) (∏ i∈s,f i) hfa hprod,
       ih hfs]
theorem sum_weightedTotalDegree_le_of_prod_dvd
   {I:Type*} [DecidableEq I] (weights:Fin 4 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 4) K) (Q:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hdiv:(∏ i∈s,f i)∣Q):
   (∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i)) ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 classical
 have hprod:(∏ i∈s,f i)≠0:=by
   intro hzero
   obtain ⟨R,hR⟩:=hdiv
   apply hQ
   rw [hR,hzero,zero_mul]
 have hf:∀ i∈s,f i≠0:=Finset.prod_ne_zero_iff.mp hprod
 rw [←weightedTotalDegree_prod_eq weights s f hf]
 exact weightedTotalDegree_le_of_dvd weights _ Q hdiv hQ
def weightEmbed3 (weights:Fin 3 → ℕ):
   (Fin 3 →₀ ℕ) →+(Fin 4 →₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+
   Finsupp.single 3 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i <;> simp [Finsupp.add_apply,map_add]
theorem weightEmbed3_original (weights:Fin 3 → ℕ)
   (d:Fin 3 →₀ ℕ) (i:Fin 3):
   weightEmbed3 weights d i.castSucc=d i:=by
 fin_cases i <;> simp [weightEmbed3]
theorem weightEmbed3_last (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   weightEmbed3 weights d (3:Fin 4)=Finsupp.weight weights d:=by
 simp [weightEmbed3]
theorem weightEmbed3_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightEmbed3 weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun a:Fin 4 →₀ ℕ↦a i.castSucc) h
 simpa only [weightEmbed3_original] using hi
def weightedLift3 (weights:Fin 3 → ℕ):
   MvPolynomial (Fin 3) K →+*MvPolynomial (Fin 4) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed3 weights)
theorem weightedLift3_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightedLift3 (K:=K) weights):=
 AddMonoidAlgebra.mapDomain_injective (weightEmbed3_injective weights)
theorem weightedLift3_ne_zero (weights:Fin 3 → ℕ)
   (P:MvPolynomial (Fin 3) K) (hP:P≠0):
   weightedLift3 weights P≠0:=by
 intro hzero
 apply hP
 apply weightedLift3_injective weights
 simpa only [map_zero] using hzero
theorem support_weightedLift3 (weights:Fin 3 → ℕ)
   (P:MvPolynomial (Fin 3) K):
   (weightedLift3 weights P).support=
     P.support.image (weightEmbed3 weights):=by
 change (Finsupp.mapDomain (weightEmbed3 weights)
     (AddMonoidAlgebra.coeff P)).support=
   Finset.image (weightEmbed3 weights) (AddMonoidAlgebra.coeff P).support
 exact Finsupp.mapDomain_support_of_injective
   (weightEmbed3_injective weights) _
theorem degree_weightedLift3 (weights:Fin 3 → ℕ)
   (P:MvPolynomial (Fin 3) K):
   (weightedLift3 weights P).degreeOf (3:Fin 4)=
     MvPolynomial.weightedTotalDegree weights P:=by
 change (weightedLift3 weights P).degreeOf (3:Fin 4)=
   P.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,support_weightedLift3,Finset.sup_image]
 apply congrArg (fun f:(Fin 3 →₀ ℕ) → ℕ↦P.support.sup f)
 funext d
 exact weightEmbed3_last weights d
theorem weightedTotalDegree_mul_fin3 (weights:Fin 3 → ℕ)
   (P Q:MvPolynomial (Fin 3) K) (hP:P≠0) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights (P*Q)=
     MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
 calc
   MvPolynomial.weightedTotalDegree weights (P*Q)=
       (weightedLift3 weights (P*Q)).degreeOf (3:Fin 4):=
     (degree_weightedLift3 weights (P*Q)).symm
   _=(weightedLift3 weights P*weightedLift3 weights Q).degreeOf
       (3:Fin 4):=by rw [map_mul]
   _=(weightedLift3 weights P).degreeOf (3:Fin 4)+
       (weightedLift3 weights Q).degreeOf (3:Fin 4):=
     MvPolynomial.degreeOf_mul_eq
       (weightedLift3_ne_zero weights P hP)
       (weightedLift3_ne_zero weights Q hQ)
   _=_:=by rw [degree_weightedLift3,degree_weightedLift3]
theorem weightedTotalDegree_le_of_dvd_fin3 (weights:Fin 3 → ℕ)
   (P Q:MvPolynomial (Fin 3) K) (hdiv:P∣Q) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights P ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 rcases hdiv with ⟨G,rfl⟩
 rcases mul_ne_zero_iff.mp hQ with ⟨hP,hG⟩
 rw [weightedTotalDegree_mul_fin3 weights P G hP hG]
 exact Nat.le_add_right _ _
theorem weightedTotalDegree_prod_eq_fin3
   {I:Type*} [DecidableEq I] (weights:Fin 3 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 3) K)
   (hf:∀ i∈s,f i≠0):
   MvPolynomial.weightedTotalDegree weights (∏ i∈s,f i)=
     ∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i):=by
 classical
 induction s using Finset.induction_on with
 | empty => simp [MvPolynomial.weightedTotalDegree]
 | @insert a s ha ih =>
     have hfa:f a≠0:=hf a (Finset.mem_insert_self a s)
     have hfs:∀ i∈s,f i≠0:=
       fun i hi↦hf i (Finset.mem_insert_of_mem hi)
     have hprod:∏ i∈s,f i≠0:=Finset.prod_ne_zero_iff.mpr hfs
     rw [Finset.prod_insert ha,Finset.sum_insert ha,
       weightedTotalDegree_mul_fin3 weights (f a) (∏ i∈s,f i)
         hfa hprod,ih hfs]
theorem sum_weightedTotalDegree_le_of_prod_dvd_fin3
   {I:Type*} [DecidableEq I] (weights:Fin 3 → ℕ) (s:Finset I)
   (f:I → MvPolynomial (Fin 3) K) (Q:MvPolynomial (Fin 3) K)
   (hQ:Q≠0) (hdiv:(∏ i∈s,f i)∣Q):
   (∑ i∈s,MvPolynomial.weightedTotalDegree weights (f i)) ≤
     MvPolynomial.weightedTotalDegree weights Q:=by
 classical
 have hprod:(∏ i∈s,f i)≠0:=by
   intro hzero
   obtain ⟨R,hR⟩:=hdiv
   apply hQ
   rw [hR,hzero,zero_mul]
 have hf:∀ i∈s,f i≠0:=Finset.prod_ne_zero_iff.mp hprod
 rw [←weightedTotalDegree_prod_eq_fin3 weights s f hf]
 exact weightedTotalDegree_le_of_dvd_fin3 weights _ Q hdiv hQ
end
end ProximityPrize.SubmissionLower.RCN071
end PackedLegacy_I4

/-! Packed from ProximityPrize.SubmissionLower.X3. -/
section PackedLegacy_X3
namespace ProximityPrize.SubmissionLower.RCN372
open scoped Classical BigOperators
noncomputable section
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def shearImage (a:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.X 0,
   MvPolynomial.X 1-MvPolynomial.C a*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def unshearImage (a:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.X 0,
   MvPolynomial.X 1+MvPolynomial.C a*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def shearAlgHom (a:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (shearImage a)
def unshearAlgHom (a:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (unshearImage a)
@[simp] theorem shearAlgHom_X (a:K) (i:Fin 3):
   shearAlgHom a (MvPolynomial.X i)=shearImage a i:=by
 simp [shearAlgHom]
@[simp] theorem unshearAlgHom_X (a:K) (i:Fin 3):
   unshearAlgHom a (MvPolynomial.X i)=unshearImage a i:=by
 simp [unshearAlgHom]
theorem unshear_comp_shear (a:K):
   (unshearAlgHom a).comp (shearAlgHom a)=AlgHom.id K (Poly3 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;> simp [shearImage,unshearImage,shearAlgHom,unshearAlgHom] <;> ring
theorem shear_comp_unshear (a:K):
   (shearAlgHom a).comp (unshearAlgHom a)=AlgHom.id K (Poly3 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;> simp [shearImage,unshearImage,shearAlgHom,unshearAlgHom] <;> ring
def shearEquiv (a:K):Poly3 K ≃ₐ[K] Poly3 K:=
 AlgEquiv.ofAlgHom (shearAlgHom a) (unshearAlgHom a)
   (shear_comp_unshear a) (unshear_comp_shear a)
@[simp] theorem shearEquiv_apply (a:K) (F:Poly3 K):
   shearEquiv a F=shearAlgHom a F:=rfl
section WeightedDegree
def weightEmbed (weights:Fin 3 → ℕ):(Fin 3 →₀ ℕ) →+(Fin 4 →₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+Finsupp.single 3 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i <;> simp [Finsupp.add_apply,map_add]
theorem weightEmbed_castSucc (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ) (i:Fin 3):
   weightEmbed weights d i.castSucc=d i:=by
 fin_cases i <;> simp [weightEmbed]
theorem weightEmbed_last (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   weightEmbed weights d (3:Fin 4)=Finsupp.weight weights d:=by
 simp [weightEmbed]
theorem weightEmbed_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightEmbed weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun b:Fin 4 →₀ ℕ↦b i.castSucc) h
 simpa only [weightEmbed_castSucc] using hi
def weightedLift (weights:Fin 3 → ℕ):Poly3 K →+*MvPolynomial (Fin 4) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed weights)
theorem weightedLift_injective (weights:Fin 3 → ℕ):
   Function.Injective (weightedLift (K:=K) weights):=
 AddMonoidAlgebra.mapDomain_injective (weightEmbed_injective weights)
theorem support_weightedLift (weights:Fin 3 → ℕ) (F:Poly3 K):
   (weightedLift weights F).support=F.support.image (weightEmbed weights):=by
 change (Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff F)).support=
   Finset.image (weightEmbed weights) (AddMonoidAlgebra.coeff F).support
 exact Finsupp.mapDomain_support_of_injective (weightEmbed_injective weights) _
theorem degree_weightedLift (weights:Fin 3 → ℕ) (F:Poly3 K):
   (weightedLift weights F).degreeOf (3:Fin 4)=
     MvPolynomial.weightedTotalDegree weights F:=by
 change (weightedLift weights F).degreeOf (3:Fin 4)=
   F.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,support_weightedLift,Finset.sup_image]
 apply congrArg (fun f:(Fin 3 →₀ ℕ) → ℕ↦F.support.sup f)
 funext d
 exact weightEmbed_last weights d
def wt (weights:Fin 3 → ℕ) (F:Poly3 K):ℕ:=
 MvPolynomial.weightedTotalDegree weights F
theorem wt_mul_le (weights:Fin 3 → ℕ) (F G:Poly3 K):
   wt weights (F*G) ≤ wt weights F+wt weights G:=by
 unfold wt
 rw [←degree_weightedLift,map_mul]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_mul_le (3:Fin 4)
     (weightedLift weights F) (weightedLift weights G)
theorem wt_sub_le (weights:Fin 3 → ℕ) (F G:Poly3 K):
   wt weights (F-G) ≤ max (wt weights F) (wt weights G):=by
 unfold wt
 rw [←degree_weightedLift,map_sub]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_sub_le (3:Fin 4)
     (weightedLift weights F) (weightedLift weights G)
theorem wt_pow_le (weights:Fin 3 → ℕ) (F:Poly3 K) (n:ℕ):
   wt weights (F^n) ≤ n*wt weights F:=by
 unfold wt
 rw [←degree_weightedLift,map_pow]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_pow_le (3:Fin 4) (weightedLift weights F) n
theorem wt_C (weights:Fin 3 → ℕ) (c:K):
   wt weights (MvPolynomial.C c:Poly3 K)=0:=by
 unfold wt MvPolynomial.weightedTotalDegree
 simp
theorem wt_X (weights:Fin 3 → ℕ) (i:Fin 3):
   wt weights (MvPolynomial.X i:Poly3 K)=weights i:=by
 unfold wt MvPolynomial.weightedTotalDegree
 simp [MvPolynomial.support_X,Finsupp.weight_single]
def pullWeights (weights:Fin 3 → ℕ):Fin 3 → ℕ:=
 ![weights 0,max (weights 1) (weights 2),weights 2]
theorem shearImage_wt_le (weights:Fin 3 → ℕ) (a:K) (i:Fin 3):
   wt weights (shearImage a i) ≤ pullWeights weights i:=by
 fin_cases i
 · simp [shearImage,pullWeights,wt_X]
 · dsimp [shearImage,pullWeights]
   have hm:=wt_mul_le weights (MvPolynomial.C a:Poly3 K) (MvPolynomial.X 2)
   rw [wt_C,Nat.zero_add,wt_X] at hm
   have hx:wt weights (MvPolynomial.X (1:Fin 3):Poly3 K)=weights 1:=
     wt_X weights 1
   exact (wt_sub_le weights (MvPolynomial.X 1)
     (MvPolynomial.C a*MvPolynomial.X 2)).trans
       (by rw [hx];exact max_le_max le_rfl hm)
 · simp [shearImage,pullWeights,wt_X]
theorem wt_finset_prod_le_sum {ι:Type*} [DecidableEq ι]
   (weights:Fin 3 → ℕ) (I:Finset ι) (f:ι → Poly3 K):
   wt weights (∏ i∈I,f i) ≤ ∑ i∈I,wt weights (f i):=by
 induction I using Finset.induction_on with
 | empty => simp [wt,MvPolynomial.weightedTotalDegree]
 | @insert i I hi ih =>
     simp only [Finset.prod_insert hi,Finset.sum_insert hi]
     exact (wt_mul_le weights (f i) (∏ j∈I,f j)).trans
       (Nat.add_le_add le_rfl ih)
theorem wt_finset_sum_le {ι:Type*} [DecidableEq ι]
   (weights:Fin 3 → ℕ) (I:Finset ι) (f:ι → Poly3 K) (cap:ℕ)
   (hf:∀ i∈I,wt weights (f i) ≤ cap):
   wt weights (∑ i∈I,f i) ≤ cap:=by
 unfold wt
 rw [←degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (3:Fin 4) I
   (fun i↦weightedLift weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [degree_weightedLift]
 exact hf i hi
theorem shear_monomial_product_wt_le
   (weights:Fin 3 → ℕ) (a:K) (d:Fin 3 →₀ ℕ):
   wt weights (∏ i∈d.support,shearImage a i^d i) ≤
     Finsupp.weight (pullWeights weights) d:=by
 apply (wt_finset_prod_le_sum weights d.support
   (fun i↦shearImage a i^d i)).trans
 calc
   (∑ i∈d.support,wt weights (shearImage a i^d i)) ≤
       ∑ i∈d.support,d i*pullWeights weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le weights (shearImage a i) (d i)).trans
       (Nat.mul_le_mul_left _ (shearImage_wt_le weights a i))
   _=Finsupp.weight (pullWeights weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
theorem shear_wt_le_pulled (weights:Fin 3 → ℕ) (a:K) (F:Poly3 K):
   wt weights (shearAlgHom a F) ≤ wt (pullWeights weights) F:=by
 change wt weights (MvPolynomial.eval₂ MvPolynomial.C (shearImage a) F) ≤ _
 rw [MvPolynomial.eval₂_eq]
 apply wt_finset_sum_le
 intro d hd
 have hprod:=shear_monomial_product_wt_le weights a d
 have hcoeff:wt weights (MvPolynomial.C (F.coeff d):Poly3 K)=0:=
   wt_C weights _
 have hmul:=wt_mul_le weights (MvPolynomial.C (F.coeff d):Poly3 K)
   (∏ i∈d.support,shearImage a i^d i)
 rw [hcoeff,Nat.zero_add] at hmul
 exact hmul.trans (hprod.trans
   (MvPolynomial.le_weightedTotalDegree (pullWeights weights) hd))
theorem weight_fin3 (weights:Fin 3 → ℕ) (d:Fin 3 →₀ ℕ):
   Finsupp.weight weights d=
     d 0*weights 0+d 1*weights 1+d 2*weights 2:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
     Finsupp.single 2 (d 2):=by
   ext i
   fin_cases i <;> simp
 rw [hd,map_add,map_add]
 simp [Finsupp.weight_single,Nat.mul_comm]
theorem two_weight_degree_le (F:Poly3 K):
   wt (![0,1,1]:Fin 3 → ℕ) F ≤ F.degreeOf 1+F.degreeOf 2:=by
 unfold wt MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 rw [weight_fin3]
 change d 0*0+d 1*1+d 2*1 ≤ _
 have h1:=MvPolynomial.le_degreeOf_of_mem_support 1 hd
 have h2:=MvPolynomial.le_degreeOf_of_mem_support 2 hd
 simp only [Nat.mul_zero,Nat.mul_one,Nat.zero_add]
 omega
end WeightedDegree
end
end ProximityPrize.SubmissionLower.RCN372
end PackedLegacy_X3

/-! Packed from ProximityPrize.SubmissionLower.Z3. -/
section PackedLegacy_Z3
namespace ProximityPrize.SubmissionLower.RCN125
open scoped Classical BigOperators
open RCN095 RCN372 RCN003 RCN002 RCN011 RCN371 RCN012 RCN013
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def flagImage (lam μ ν:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.X 0-MvPolynomial.C lam*MvPolynomial.X 2,
   MvPolynomial.X 1-
     (MvPolynomial.C μ*MvPolynomial.X 0-
       MvPolynomial.C (μ*lam-ν)*MvPolynomial.X 2),
   MvPolynomial.X 2] i
def unflagImage (lam μ ν:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.X 0+MvPolynomial.C lam*MvPolynomial.X 2,
   MvPolynomial.X 1+MvPolynomial.C μ*MvPolynomial.X 0+
     MvPolynomial.C ν*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def flagAlgHom (lam μ ν:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (flagImage lam μ ν)
def unflagAlgHom (lam μ ν:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (unflagImage lam μ ν)
@[simp] theorem flagAlgHom_X (lam μ ν:K) (i:Fin 3):
   flagAlgHom lam μ ν (MvPolynomial.X i)=flagImage lam μ ν i:=by
 simp [flagAlgHom]
@[simp] theorem unflagAlgHom_X (lam μ ν:K) (i:Fin 3):
   unflagAlgHom lam μ ν (MvPolynomial.X i)=unflagImage lam μ ν i:=by
 simp [unflagAlgHom]
theorem unflag_comp_flag (lam μ ν:K):
   (unflagAlgHom lam μ ν).comp (flagAlgHom lam μ ν)=
     AlgHom.id K (Poly3 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [flagImage,unflagImage,flagAlgHom,unflagAlgHom] <;> ring
theorem flag_comp_unflag (lam μ ν:K):
   (flagAlgHom lam μ ν).comp (unflagAlgHom lam μ ν)=
     AlgHom.id K (Poly3 K):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [flagImage,unflagImage,flagAlgHom,unflagAlgHom] <;> ring
def flagEquiv (lam μ ν:K):Poly3 K ≃ₐ[K] Poly3 K:=
 AlgEquiv.ofAlgHom (flagAlgHom lam μ ν) (unflagAlgHom lam μ ν)
   (flag_comp_unflag lam μ ν) (unflag_comp_flag lam μ ν)
@[simp] theorem flagEquiv_apply (lam μ ν:K) (F:Poly3 K):
   flagEquiv lam μ ν F=flagAlgHom lam μ ν F:=rfl
theorem flag_irreducible_iff (lam μ ν:K) (F:Poly3 K):
   Irreducible (flagAlgHom lam μ ν F) ↔ Irreducible F:=by
 simpa only [flagEquiv_apply] using
   (MulEquiv.irreducible_iff (flagEquiv lam μ ν))
theorem flag_dvd_iff (lam μ ν:K) (F G:Poly3 K):
   flagAlgHom lam μ ν F∣flagAlgHom lam μ ν G ↔ F∣G:=by
 simpa only [flagEquiv_apply] using
   (map_dvd_iff (flagEquiv lam μ ν))
theorem flag_ne_zero (lam μ ν:K) {F:Poly3 K} (hF:F≠0):
   flagAlgHom lam μ ν F≠0:=
 (flagEquiv lam μ ν).injective.ne hF
theorem eval₂Hom_flag
   {A:Type} [CommRing A] [Algebra K A]
   (F:Poly3 K) (u v z:A) (lam μ ν:K):
   MvPolynomial.eval₂Hom (algebraMap K A) ![u,v,z]
       (flagAlgHom lam μ ν F)=
     MvPolynomial.eval₂Hom (algebraMap K A)
       ![u-algebraMap K A lam*z,
         v-algebraMap K A μ*u+
           algebraMap K A (μ*lam-ν)*z,
         z] F:=by
 have hhom:
     (MvPolynomial.eval₂Hom (algebraMap K A) ![u,v,z]).comp
         (flagAlgHom lam μ ν).toRingHom=
       MvPolynomial.eval₂Hom (algebraMap K A)
         ![u-algebraMap K A lam*z,
           v-algebraMap K A μ*u+
             algebraMap K A (μ*lam-ν)*z,
           z]:=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp [RingHom.comp_apply,flagAlgHom]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,flagAlgHom,flagImage] <;> ring
 exact RingHom.congr_fun hhom F
theorem eval₂Hom_flag_at_affine
   {A:Type} [CommRing A] [Algebra K A]
   (F:Poly3 K) (y s z:A) (lam μ ν:K):
   MvPolynomial.eval₂Hom (algebraMap K A)
       ![y+algebraMap K A lam*z,
         s+algebraMap K A μ*y+algebraMap K A ν*z,
         z] (flagAlgHom lam μ ν F)=
     MvPolynomial.eval₂Hom (algebraMap K A) ![y,s,z] F:=by
 rw [eval₂Hom_flag]
 congr 2
 funext i
 fin_cases i <;> simp <;> ring
def flagPullWeights (weights:Fin 3 → ℕ):Fin 3 → ℕ:=
 ![max (weights 0) (weights 2),
   max (weights 1) (max (weights 0) (weights 2)),
   weights 2]
theorem flagImage_wt_le (weights:Fin 3 → ℕ) (lam μ ν:K) (i:Fin 3):
   wt weights (flagImage lam μ ν i) ≤ flagPullWeights weights i:=by
 fin_cases i
 · dsimp [flagImage,flagPullWeights]
   have hm:=wt_mul_le weights (MvPolynomial.C lam:Poly3 K)
     (MvPolynomial.X 2)
   rw [wt_C,Nat.zero_add,wt_X] at hm
   exact (wt_sub_le weights (MvPolynomial.X 0)
     (MvPolynomial.C lam*MvPolynomial.X 2)).trans
       (max_le_max (by rw [wt_X]) hm)
 · dsimp [flagImage,flagPullWeights]
   have hμ:=wt_mul_le weights (MvPolynomial.C μ:Poly3 K)
     (MvPolynomial.X 0)
   have hν:=wt_mul_le weights (MvPolynomial.C (μ*lam-ν):Poly3 K)
     (MvPolynomial.X 2)
   rw [wt_C,Nat.zero_add,wt_X] at hμ hν
   have hinner:=wt_sub_le weights
     (MvPolynomial.C μ*MvPolynomial.X 0)
     (MvPolynomial.C (μ*lam-ν)*MvPolynomial.X 2)
   have houter:=wt_sub_le weights (MvPolynomial.X 1)
     (MvPolynomial.C μ*MvPolynomial.X 0-
       MvPolynomial.C (μ*lam-ν)*MvPolynomial.X 2)
   exact houter.trans (max_le_max (by rw [wt_X])
     (hinner.trans (max_le_max hμ hν)))
 · simp [flagImage,flagPullWeights,wt_X]
theorem flag_monomial_product_wt_le
   (weights:Fin 3 → ℕ) (lam μ ν:K) (d:Fin 3 →₀ ℕ):
   wt weights (∏ i∈d.support,flagImage lam μ ν i^d i) ≤
     Finsupp.weight (flagPullWeights weights) d:=by
 apply (wt_finset_prod_le_sum weights d.support
   (fun i↦flagImage lam μ ν i^d i)).trans
 calc
   (∑ i∈d.support,wt weights (flagImage lam μ ν i^d i)) ≤
       ∑ i∈d.support,d i*flagPullWeights weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le weights (flagImage lam μ ν i) (d i)).trans
       (Nat.mul_le_mul_left _ (flagImage_wt_le weights lam μ ν i))
   _=Finsupp.weight (flagPullWeights weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
theorem flagAlgHom_wt_le_pulled
   (weights:Fin 3 → ℕ) (lam μ ν:K) (F:Poly3 K):
   wt weights (flagAlgHom lam μ ν F) ≤ wt (flagPullWeights weights) F:=by
 change wt weights
     (MvPolynomial.eval₂ MvPolynomial.C (flagImage lam μ ν) F) ≤ _
 rw [MvPolynomial.eval₂_eq]
 apply wt_finset_sum_le
 intro d hd
 have hprod:=flag_monomial_product_wt_le weights lam μ ν d
 have hcoeff:wt weights (MvPolynomial.C (F.coeff d):Poly3 K)=0:=
   wt_C weights _
 have hmul:=wt_mul_le weights (MvPolynomial.C (F.coeff d):Poly3 K)
   (∏ i∈d.support,flagImage lam μ ν i^d i)
 rw [hcoeff,Nat.zero_add] at hmul
 exact hmul.trans (hprod.trans
   (MvPolynomial.le_weightedTotalDegree (flagPullWeights weights) hd))
def sWeight:Fin 3 → ℕ:=![0,1,0]
def ysWeight:Fin 3 → ℕ:=![1,1,0]
def totalWeight:Fin 3 → ℕ:=![1,1,1]
@[simp] theorem flagPullWeights_sWeight:flagPullWeights sWeight=sWeight:=by
 funext i
 fin_cases i <;> simp [flagPullWeights,sWeight]
@[simp] theorem flagPullWeights_ysWeight:flagPullWeights ysWeight=ysWeight:=by
 funext i
 fin_cases i <;> simp [flagPullWeights,ysWeight]
@[simp] theorem flagPullWeights_totalWeight:
   flagPullWeights totalWeight=totalWeight:=by
 funext i
 fin_cases i <;> simp [flagPullWeights,totalWeight]
def PolynomialInFlag (p:FlagDegree) (F:Poly3 K):Prop:=
 ∀ d∈F.support,InFlag p d
theorem wt_s_le_of_inFlag {p:FlagDegree} {F:Poly3 K}
   (hF:PolynomialInFlag p F):wt sWeight F ≤ p.all:=by
 unfold wt MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 have h:=(hF d hd).1
 simpa [sWeight,weight_fin3] using h
theorem wt_ys_le_of_inFlag {p:FlagDegree} {F:Poly3 K}
   (hF:PolynomialInFlag p F):wt ysWeight F ≤ p.yz+p.all:=by
 unfold wt MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 have h:=(hF d hd).2.1
 simpa [ysWeight,weight_fin3,Nat.add_comm] using h
theorem wt_total_le_of_inFlag {p:FlagDegree} {F:Poly3 K}
   (hF:PolynomialInFlag p F):
   wt totalWeight F ≤ p.zOnly+p.yz+p.all:=by
 unfold wt MvPolynomial.weightedTotalDegree
 apply Finset.sup_le
 intro d hd
 have h:=(hF d hd).2.2
 simpa [totalWeight,weight_fin3,Nat.add_comm,Nat.add_left_comm,
   Nat.add_assoc] using h
theorem polynomialInFlag_flagAlgHom
   (p:FlagDegree) (F:Poly3 K) (lam μ ν:K)
   (hF:PolynomialInFlag p F):
   PolynomialInFlag p (flagAlgHom lam μ ν F):=by
 intro d hd
 have hs:=MvPolynomial.le_weightedTotalDegree sWeight hd
 have hys:=MvPolynomial.le_weightedTotalDegree ysWeight hd
 have htot:=MvPolynomial.le_weightedTotalDegree totalWeight hd
 have hsw:=(flagAlgHom_wt_le_pulled sWeight lam μ ν F).trans
   (by simpa using wt_s_le_of_inFlag hF)
 have hysw:=(flagAlgHom_wt_le_pulled ysWeight lam μ ν F).trans
   (by simpa using wt_ys_le_of_inFlag hF)
 have htotw:=(flagAlgHom_wt_le_pulled totalWeight lam μ ν F).trans
   (by simpa using wt_total_le_of_inFlag hF)
 refine ⟨?_,?_,?_⟩
 · have:=hs.trans hsw
   simpa [sWeight,weight_fin3] using this
 · have:=hys.trans hysw
   simpa [ysWeight,weight_fin3,Nat.add_comm] using this
 · have:=htot.trans htotw
   simpa [totalWeight,weight_fin3,Nat.add_comm,Nat.add_left_comm,
     Nat.add_assoc] using this
def uOrder:Fin 3 ≃ Fin 3:=Equiv.refl _
def vOrder:Fin 3 ≃ Fin 3:=Equiv.swap 0 1
def zOrder:Fin 3 ≃ Fin 3:=Equiv.swap 0 2
structure FlagJointCertificateProvider
   (lam μ ν:K) (G H:Poly3 K) (p:ℕ):Prop where
 u:JointOrderCertificate K uOrder
   (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H) p
 v:JointOrderCertificate K vOrder
   (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H) p
 z:JointOrderCertificate K zOrder
   (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H) p
end
end ProximityPrize.SubmissionLower.RCN125
end PackedLegacy_Z3

/-! Packed from ProximityPrize.SubmissionLower.B9. -/
section PackedLegacy_B9
namespace ProximityPrize.SubmissionLower.RCN094
open scoped Classical BigOperators
open RCN095 RCN372
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def residualImage (aY v bY aS bS cS:K) (i:Fin 3):Poly3 K:=
 ![MvPolynomial.C aY+MvPolynomial.C v*MvPolynomial.X 0+
     MvPolynomial.C bY*MvPolynomial.X 2,
   MvPolynomial.C aS+MvPolynomial.C v*MvPolynomial.X 1+
     MvPolynomial.C bS*MvPolynomial.X 0+
     MvPolynomial.C cS*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def originalImage (aY v bY aS bS cS:K) (i:Fin 3):Poly3 K:=
 let y:=MvPolynomial.C v⁻¹*
   (MvPolynomial.X 0-MvPolynomial.C aY-
     MvPolynomial.C bY*MvPolynomial.X 2)
 ![y,
   MvPolynomial.C v⁻¹*
     (MvPolynomial.X 1-MvPolynomial.C aS-
       MvPolynomial.C bS*y-MvPolynomial.C cS*MvPolynomial.X 2),
   MvPolynomial.X 2] i
def residualAlgHom (aY v bY aS bS cS:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (residualImage aY v bY aS bS cS)
def originalAlgHom (aY v bY aS bS cS:K):Poly3 K →ₐ[K] Poly3 K:=
 MvPolynomial.aeval (originalImage aY v bY aS bS cS)
@[simp] theorem residualAlgHom_X
   (aY v bY aS bS cS:K) (i:Fin 3):
   residualAlgHom aY v bY aS bS cS (MvPolynomial.X i)=
     residualImage aY v bY aS bS cS i:=by
 simp [residualAlgHom]
@[simp] theorem originalAlgHom_X
   (aY v bY aS bS cS:K) (i:Fin 3):
   originalAlgHom aY v bY aS bS cS (MvPolynomial.X i)=
     originalImage aY v bY aS bS cS i:=by
 simp [originalAlgHom]
theorem original_comp_residual
   (aY v bY aS bS cS:K) (hv:v≠0):
   (originalAlgHom aY v bY aS bS cS).comp
       (residualAlgHom aY v bY aS bS cS)=
     AlgHom.id K (Poly3 K):=by
 have hvC:(MvPolynomial.C v:Poly3 K)*MvPolynomial.C v⁻¹=1:=by
   rw [←map_mul]
   simp [hv]
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
   linear_combination
     (MvPolynomial.X 0-MvPolynomial.C bY*MvPolynomial.X 2-
       MvPolynomial.C aY)*hvC
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
   linear_combination
     (MvPolynomial.X 1-MvPolynomial.C cS*MvPolynomial.X 2-
       (MvPolynomial.C aS+MvPolynomial.C v⁻¹*MvPolynomial.C bS*
         (MvPolynomial.X 0-MvPolynomial.C aY-
           MvPolynomial.C bY*MvPolynomial.X 2)))*hvC
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
theorem residual_comp_original
   (aY v bY aS bS cS:K) (hv:v≠0):
   (residualAlgHom aY v bY aS bS cS).comp
       (originalAlgHom aY v bY aS bS cS)=
     AlgHom.id K (Poly3 K):=by
 have hvC:(MvPolynomial.C v⁻¹:Poly3 K)*MvPolynomial.C v=1:=by
   rw [←map_mul]
   simp [hv]
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
   linear_combination MvPolynomial.X 0*hvC
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
   linear_combination
     (MvPolynomial.X 1-
       MvPolynomial.C v⁻¹*MvPolynomial.C bS*MvPolynomial.X 0)*hvC
 · simp [residualImage,originalImage,residualAlgHom,originalAlgHom]
def residualEquiv (aY v bY aS bS cS:K) (hv:v≠0):
   Poly3 K ≃ₐ[K] Poly3 K:=
 AlgEquiv.ofAlgHom
   (residualAlgHom aY v bY aS bS cS)
   (originalAlgHom aY v bY aS bS cS)
   (residual_comp_original aY v bY aS bS cS hv)
   (original_comp_residual aY v bY aS bS cS hv)
@[simp] theorem residualEquiv_apply
   (aY v bY aS bS cS:K) (hv:v≠0) (F:Poly3 K):
   residualEquiv aY v bY aS bS cS hv F=
     residualAlgHom aY v bY aS bS cS F:=rfl
theorem residual_irreducible_iff
   (aY v bY aS bS cS:K) (hv:v≠0) (F:Poly3 K):
   Irreducible (residualAlgHom aY v bY aS bS cS F) ↔ Irreducible F:=by
 simpa only [residualEquiv_apply] using
   (MulEquiv.irreducible_iff (residualEquiv aY v bY aS bS cS hv))
theorem residual_dvd_iff
   (aY v bY aS bS cS:K) (hv:v≠0) (F G:Poly3 K):
   residualAlgHom aY v bY aS bS cS F∣
       residualAlgHom aY v bY aS bS cS G ↔ F∣G:=by
 simpa only [residualEquiv_apply] using
   (map_dvd_iff (residualEquiv aY v bY aS bS cS hv))
theorem eval₂Hom_residual
   {A:Type} [CommRing A] [Algebra K A]
   (F:Poly3 K) (y s z:A) (aY v bY aS bS cS:K):
   MvPolynomial.eval₂Hom (algebraMap K A) ![y,s,z]
       (residualAlgHom aY v bY aS bS cS F)=
     MvPolynomial.eval₂Hom (algebraMap K A)
       ![algebraMap K A aY+algebraMap K A v*y+
           algebraMap K A bY*z,
         algebraMap K A aS+algebraMap K A v*s+
           algebraMap K A bS*y+algebraMap K A cS*z,
         z] F:=by
 have hhom:
     (MvPolynomial.eval₂Hom (algebraMap K A) ![y,s,z]).comp
         (residualAlgHom aY v bY aS bS cS).toRingHom=
       MvPolynomial.eval₂Hom (algebraMap K A)
         ![algebraMap K A aY+algebraMap K A v*y+
             algebraMap K A bY*z,
           algebraMap K A aS+algebraMap K A v*s+
             algebraMap K A bS*y+algebraMap K A cS*z,
           z]:=by
   apply MvPolynomial.ringHom_ext
   · intro c
     simp [RingHom.comp_apply,residualAlgHom]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,residualAlgHom,residualImage] <;> ring
 exact RingHom.congr_fun hhom F
theorem wt_add_le_residual
   (weights:Fin 3 → ℕ) (F G:Poly3 K):
   wt weights (F+G) ≤ max (wt weights F) (wt weights G):=by
 unfold wt
 rw [←degree_weightedLift,map_add]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_add_le (3:Fin 4)
     (weightedLift weights F) (weightedLift weights G)
theorem residualImage_wt_le
   (weights:Fin 3 → ℕ) (aY v bY aS bS cS:K) (i:Fin 3):
   wt weights (residualImage aY v bY aS bS cS i) ≤
     RCN125.flagPullWeights weights i:=by
 fin_cases i
 · dsimp [residualImage,
     RCN125.flagPullWeights]
   have hvx:=wt_mul_le weights (MvPolynomial.C v:Poly3 K)
     (MvPolynomial.X 0)
   have hbx:=wt_mul_le weights (MvPolynomial.C bY:Poly3 K)
     (MvPolynomial.X 2)
   rw [wt_C,Nat.zero_add,wt_X] at hvx hbx
   have hleft:=wt_add_le_residual weights (MvPolynomial.C aY:Poly3 K)
     (MvPolynomial.C v*MvPolynomial.X 0)
   have hall:=wt_add_le_residual weights
     (MvPolynomial.C aY+MvPolynomial.C v*MvPolynomial.X 0:Poly3 K)
     (MvPolynomial.C bY*MvPolynomial.X 2)
   rw [wt_C] at hleft
   exact hall.trans (by omega)
 · dsimp [residualImage,
     RCN125.flagPullWeights]
   have hvx:=wt_mul_le weights (MvPolynomial.C v:Poly3 K)
     (MvPolynomial.X 1)
   have hbx:=wt_mul_le weights (MvPolynomial.C bS:Poly3 K)
     (MvPolynomial.X 0)
   have hcx:=wt_mul_le weights (MvPolynomial.C cS:Poly3 K)
     (MvPolynomial.X 2)
   rw [wt_C,Nat.zero_add,wt_X] at hvx hbx hcx
   have h0:=wt_add_le_residual weights (MvPolynomial.C aS:Poly3 K)
     (MvPolynomial.C v*MvPolynomial.X 1)
   have h1:=wt_add_le_residual weights
     (MvPolynomial.C aS+MvPolynomial.C v*MvPolynomial.X 1:Poly3 K)
     (MvPolynomial.C bS*MvPolynomial.X 0)
   have h2:=wt_add_le_residual weights
     (MvPolynomial.C aS+MvPolynomial.C v*MvPolynomial.X 1+
       MvPolynomial.C bS*MvPolynomial.X 0:Poly3 K)
     (MvPolynomial.C cS*MvPolynomial.X 2)
   rw [wt_C] at h0
   exact h2.trans (by omega)
 · simp [residualImage,
     RCN125.flagPullWeights,wt_X]
theorem residual_monomial_product_wt_le
   (weights:Fin 3 → ℕ) (aY v bY aS bS cS:K)
   (d:Fin 3 →₀ ℕ):
   wt weights
       (∏ i∈d.support,residualImage aY v bY aS bS cS i^d i) ≤
     Finsupp.weight
       (RCN125.flagPullWeights weights) d:=by
 apply (wt_finset_prod_le_sum weights d.support
   (fun i↦residualImage aY v bY aS bS cS i^d i)).trans
 calc
   (∑ i∈d.support,
       wt weights (residualImage aY v bY aS bS cS i^d i)) ≤
       ∑ i∈d.support,d i*
         RCN125.flagPullWeights weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le weights (residualImage aY v bY aS bS cS i) (d i)).trans
       (Nat.mul_le_mul_left _
         (residualImage_wt_le weights aY v bY aS bS cS i))
   _=Finsupp.weight
       (RCN125.flagPullWeights weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
theorem residualAlgHom_wt_le_pulled
   (weights:Fin 3 → ℕ) (aY v bY aS bS cS:K) (F:Poly3 K):
   wt weights (residualAlgHom aY v bY aS bS cS F) ≤
     wt (RCN125.flagPullWeights weights) F:=by
 change wt weights
     (MvPolynomial.eval₂ MvPolynomial.C
       (residualImage aY v bY aS bS cS) F) ≤ _
 rw [MvPolynomial.eval₂_eq]
 apply wt_finset_sum_le
 intro d hd
 have hprod:=residual_monomial_product_wt_le weights
   aY v bY aS bS cS d
 have hcoeff:
     wt weights (MvPolynomial.C (F.coeff d):Poly3 K)=0:=wt_C weights _
 have hmul:=wt_mul_le weights (MvPolynomial.C (F.coeff d):Poly3 K)
   (∏ i∈d.support,residualImage aY v bY aS bS cS i^d i)
 rw [hcoeff,Nat.zero_add] at hmul
 exact hmul.trans (hprod.trans
   (MvPolynomial.le_weightedTotalDegree
     (RCN125.flagPullWeights weights) hd))
theorem polynomialInFlag_residualAlgHom
   (p:FlagDegree) (F:Poly3 K) (aY v bY aS bS cS:K)
   (hF:RCN125.PolynomialInFlag p F):
   RCN125.PolynomialInFlag p
     (residualAlgHom aY v bY aS bS cS F):=by
 intro d hd
 let sWeight:=RCN125.sWeight
 let ysWeight:=RCN125.ysWeight
 let totalWeight:=RCN125.totalWeight
 have hs:=MvPolynomial.le_weightedTotalDegree sWeight hd
 have hys:=MvPolynomial.le_weightedTotalDegree ysWeight hd
 have htot:=MvPolynomial.le_weightedTotalDegree totalWeight hd
 have hsw:=(residualAlgHom_wt_le_pulled sWeight
   aY v bY aS bS cS F).trans (by
     simpa [sWeight] using
       RCN125.wt_s_le_of_inFlag hF)
 have hysw:=(residualAlgHom_wt_le_pulled ysWeight
   aY v bY aS bS cS F).trans (by
     simpa [ysWeight] using
       RCN125.wt_ys_le_of_inFlag hF)
 have htotw:=(residualAlgHom_wt_le_pulled totalWeight
   aY v bY aS bS cS F).trans (by
     simpa [totalWeight] using
       RCN125.wt_total_le_of_inFlag hF)
 refine ⟨?_,?_,?_⟩
 · have:=hs.trans hsw
   simpa [sWeight,RCN125.sWeight,
     weight_fin3] using this
 · have:=hys.trans hysw
   simpa [ysWeight,RCN125.ysWeight,
     weight_fin3,
     Nat.add_comm] using this
 · have:=htot.trans htotw
   simpa [totalWeight,RCN125.totalWeight,
     weight_fin3,
     Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using this
end
end ProximityPrize.SubmissionLower.RCN094
end PackedLegacy_B9

/-! Packed from ProximityPrize.SubmissionLower.K4. -/
section PackedLegacy_K4
namespace ProximityPrize.SubmissionLower.RCN161
noncomputable section
open scoped Function
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
variable {K:Type*} [Field K]
theorem nodal_dvd_of_eval_eq_zero
   {ι:Type*} (I:Finset ι) (x:ι → K)
   (hinj:Set.InjOn x I) (P:Polynomial K)
   (hzero:∀ i∈I,P.eval (x i)=0):
   Lagrange.nodal I x∣P:=by
 classical
 rw [Lagrange.nodal_eq]
 apply Finset.prod_dvd_of_coprime
 · intro i hi j hj hij
   exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
     (sub_ne_zero.mpr (fun hxy => hij (hinj hi hj hxy))).isUnit
 · intro i hi
   rw [Polynomial.dvd_iff_isRoot,Polynomial.IsRoot]
   exact hzero i hi
variable {L:Type*} [Field L]
end
end ProximityPrize.SubmissionLower.RCN161
end PackedLegacy_K4

/-! Packed from ProximityPrize.SubmissionLower.EZ. -/
section PackedLegacy_EZ
namespace ProximityPrize.SubmissionLower.RCN160
open RCN238
noncomputable section
variable {K ι:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι
theorem nodal_eval_ne_zero_of_mem_sdiff
   (I nodes:Finset ι) (x:ι → K)
   (hsub:I ⊆ nodes) (hinj:Set.InjOn x nodes)
   {j:ι} (hj:j∈nodes \ I):
   (Lagrange.nodal I x).eval (x j)≠0:=by
 apply Lagrange.eval_nodal_not_at_node
 intro i hi hji
 have hji':j=i:=hinj (Finset.mem_sdiff.mp hj).1 (hsub hi) hji
 exact (Finset.mem_sdiff.mp hj).2 (hji' ▸ hi)
def residualReceived
   (I:Finset ι) (x u:ι → K) (P:Polynomial K) (j:ι):K:=
 (u j-P.eval (x j))/(Lagrange.nodal I x).eval (x j)
theorem residual_agreement_of_original
   (I nodes:Finset ι) (x u0 u1:ι → K)
   (hsub:I ⊆ nodes) (hinj:Set.InjOn x nodes)
   (P0 P1 C S:Polynomial K) (gamma:K)
   (hnormal:S=P0+Polynomial.C gamma*P1+Lagrange.nodal I x*C)
   {j:ι} (hj:j∈nodes \ I)
   (hagree:S.eval (x j)=u0 j+gamma*u1 j):
   C.eval (x j)=residualReceived I x u0 P0 j+
     gamma*residualReceived I x u1 P1 j:=by
 have hV:=nodal_eval_ne_zero_of_mem_sdiff I nodes x hsub hinj hj
 have heval:=congrArg (fun P:Polynomial K↦P.eval (x j)) hnormal
 simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] at heval
 unfold residualReceived
 field_simp [hV]
 linear_combination hagree-heval
theorem noLargeSelectedPencil_residual
   (I:Finset ι) (x:ι → K) (w e:ℕ) (hIw:I.card ≤ w)
   (selected residual:K → Polynomial K) (Gamma:Finset K)
   (P0 P1:Polynomial K) (hP0:P0.natDegree ≤ w)
   (hP1:P1.natDegree ≤ w)
   (hnormal:∀ gamma∈Gamma,
     selected gamma=P0+Polynomial.C gamma*P1+
       Lagrange.nodal I x*residual gamma)
   (hno:NoLargeSelectedPencil selected Gamma w e):
   NoLargeSelectedPencil residual Gamma (w-I.card) e:=by
 intro A B hA hB
 let V:=Lagrange.nodal I x
 let A0:=P0+V*A
 let B0:=P1+V*B
 have hV:V.natDegree=I.card:=by
   exact Lagrange.natDegree_nodal
 have hVA:(V*A).natDegree ≤ w:=by
   calc
     (V*A).natDegree ≤ V.natDegree+A.natDegree:=
       Polynomial.natDegree_mul_le
     _ ≤ I.card+(w-I.card):=by omega
     _=w:=Nat.add_sub_of_le hIw
 have hVB:(V*B).natDegree ≤ w:=by
   calc
     (V*B).natDegree ≤ V.natDegree+B.natDegree:=
       Polynomial.natDegree_mul_le
     _ ≤ I.card+(w-I.card):=by omega
     _=w:=Nat.add_sub_of_le hIw
 have hA0:A0.natDegree ≤ w:=by
   exact (Polynomial.natDegree_add_le _ _).trans (max_le hP0 hVA)
 have hB0:B0.natDegree ≤ w:=by
   exact (Polynomial.natDegree_add_le _ _).trans (max_le hP1 hVB)
 calc
   (Gamma.filter (fun gamma↦
     residual gamma=A+Polynomial.C gamma*B)).card ≤
       (Gamma.filter (fun gamma↦
         selected gamma=A0+Polynomial.C gamma*B0)).card:=by
     apply Finset.card_le_card
     intro gamma hgamma
     obtain ⟨hGamma,hpencil⟩:=Finset.mem_filter.mp hgamma
     apply Finset.mem_filter.mpr
     refine ⟨hGamma,?_⟩
     rw [hnormal gamma hGamma,hpencil]
     simp only [A0,B0,V]
     ring
   _ ≤ e+1:=hno A0 B0 hA0 hB0
end
end ProximityPrize.SubmissionLower.RCN160
end PackedLegacy_EZ

/-! Packed from ProximityPrize.SubmissionLower.EX. -/
section PackedLegacy_EX
namespace ProximityPrize.SubmissionLower.RCN155
open RCN238 RCN161 RCN160
noncomputable section
variable {K ι:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι
theorem exists_common_affine_nodal_residual_family
   (I:Finset ι) (x u0 u1:ι → K)
   (w:ℕ) (hIw:I.card ≤ w) (hinj:Set.InjOn x I)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hvalues:∀ gamma∈Gamma,∀ i∈I,
     (selected gamma).eval (x i)=u0 i+gamma*u1 i):
   ∃ P0 P1:Polynomial K,∃ residual:K → Polynomial K,
     P0.natDegree ≤ w∧P1.natDegree ≤ w∧
     (∀ gamma∈Gamma,(residual gamma).natDegree ≤ w-I.card)∧
     ∀ gamma∈Gamma,
       selected gamma=P0+Polynomial.C gamma*P1+
         Lagrange.nodal I x*residual gamma:=by
 classical
 let P0:Polynomial K:=Lagrange.interpolate I x u0
 let P1:Polynomial K:=Lagrange.interpolate I x u1
 let V:Polynomial K:=Lagrange.nodal I x
 let D:K → Polynomial K:=fun gamma↦
   selected gamma-(P0+Polynomial.C gamma*P1)
 have hpredw:I.card-1 ≤ w:=(Nat.sub_le I.card 1).trans hIw
 have hP0:P0.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   exact (Lagrange.degree_interpolate_le u0 hinj).trans
     (WithBot.coe_le_coe.mpr hpredw)
 have hP1:P1.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   exact (Lagrange.degree_interpolate_le u1 hinj).trans
     (WithBot.coe_le_coe.mpr hpredw)
 have hDdegree:∀ gamma∈Gamma,(D gamma).natDegree ≤ w:=by
   intro gamma hgamma
   apply (Polynomial.natDegree_sub_le _ _).trans
   exact max_le (hdegree gamma hgamma)
     ((Polynomial.natDegree_add_le _ _).trans
       (max_le hP0 ((Polynomial.natDegree_C_mul_le gamma P1).trans hP1)))
 have hDeval:∀ gamma∈Gamma,∀ i∈I,
     (D gamma).eval (x i)=0:=by
   intro gamma hgamma i hi
   simp only [D,Polynomial.eval_sub,Polynomial.eval_add,
     Polynomial.eval_mul,Polynomial.eval_C]
   rw [Lagrange.eval_interpolate_at_node u0 hinj hi,
     Lagrange.eval_interpolate_at_node u1 hinj hi,
     hvalues gamma hgamma i hi]
   ring
 have hdvd:∀ gamma,gamma∈Gamma → V∣D gamma:=by
   intro gamma hgamma
   exact nodal_dvd_of_eval_eq_zero I x hinj (D gamma)
     (hDeval gamma hgamma)
 let residual:K → Polynomial K:=fun gamma↦
   if hgamma:gamma∈Gamma then (hdvd gamma hgamma).choose else 0
 have hfactor:∀ gamma∈Gamma,
     D gamma=V*residual gamma:=by
   intro gamma hgamma
   dsimp only [residual]
   rw [dif_pos hgamma]
   exact (hdvd gamma hgamma).choose_spec
 have hresidualDegree:∀ gamma∈Gamma,
     (residual gamma).natDegree ≤ w-I.card:=by
   intro gamma hgamma
   by_cases hzero:residual gamma=0
   · simp [hzero]
   · have hdegmul:(V*residual gamma).natDegree=
         I.card+(residual gamma).natDegree:=by
       rw [(Lagrange.nodal_monic (s:=I) (v:=x)).natDegree_mul' hzero,
         Lagrange.natDegree_nodal]
     have hmul:(V*residual gamma).natDegree ≤ w:=by
       rw [←hfactor gamma hgamma]
       exact hDdegree gamma hgamma
     rw [hdegmul] at hmul
     omega
 refine ⟨P0,P1,residual,hP0,hP1,hresidualDegree,?_⟩
 intro gamma hgamma
 have hf:=hfactor gamma hgamma
 change selected gamma=P0+Polynomial.C gamma*P1+V*residual gamma
 change selected gamma-(P0+Polynomial.C gamma*P1)=
   V*residual gamma at hf
 linear_combination hf
theorem exists_residual_family_with_incidence_data
   (I nodes:Finset ι) (x u0 u1:ι → K)
   (w e:ℕ) (hsub:I ⊆ nodes) (hIw:I.card ≤ w)
   (hinj:Set.InjOn x nodes)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hvalues:∀ gamma∈Gamma,∀ i∈I,
     (selected gamma).eval (x i)=u0 i+gamma*u1 i)
   (hno:NoLargeSelectedPencil selected Gamma w e):
   ∃ P0 P1:Polynomial K,∃ residual:K → Polynomial K,
     P0.natDegree ≤ w∧P1.natDegree ≤ w∧
     (∀ gamma∈Gamma,(residual gamma).natDegree ≤ w-I.card)∧
     NoLargeSelectedPencil residual Gamma (w-I.card) e∧
     (∀ gamma∈Gamma,
       selected gamma=P0+Polynomial.C gamma*P1+
         Lagrange.nodal I x*residual gamma)∧
     ∀ gamma∈Gamma,∀ j∈nodes \ I,
       (selected gamma).eval (x j)=u0 j+gamma*u1 j →
         (residual gamma).eval (x j)=
           residualReceived (K:=K) I x u0 P0 j+
             gamma*residualReceived (K:=K) I x u1 P1 j:=by
 have hIinj:Set.InjOn x I:=hinj.mono hsub
 obtain ⟨P0,P1,residual,hP0,hP1,hresdeg,hnormal⟩:=
   exists_common_affine_nodal_residual_family I x u0 u1 w hIw hIinj
     selected Gamma hdegree hvalues
 have hnores:NoLargeSelectedPencil residual Gamma (w-I.card) e:=
   noLargeSelectedPencil_residual I x w e hIw selected residual Gamma
     P0 P1 hP0 hP1 hnormal hno
 refine ⟨P0,P1,residual,hP0,hP1,hresdeg,hnores,hnormal,?_⟩
 intro gamma hgamma j hj hagree
 exact residual_agreement_of_original I nodes x u0 u1 hsub hinj
   P0 P1 (residual gamma) (selected gamma) gamma
   (hnormal gamma hgamma) hj hagree
end
end ProximityPrize.SubmissionLower.RCN155
end PackedLegacy_EX

/-! Packed from ProximityPrize.SubmissionLower.BQ. -/
section PackedLegacy_BQ
namespace ProximityPrize.SubmissionLower.RCN163
open scoped Classical
open RCN094 RCN157 RCN155 RCN160 RCN238 RCN125 RCN372
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega]
local instance:DecidableEq Omega:=Classical.decEq Omega
end
end ProximityPrize.SubmissionLower.RCN163
end PackedLegacy_BQ
end Compact_PackedLegacyCore1
