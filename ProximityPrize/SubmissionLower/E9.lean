import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.P2
import ProximityPrize.SubmissionLower.BD
import ProximityPrize.SubmissionLower.K
namespace ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch
open scoped BigOperators
open ProximityPrize.Benchmark
open ContactSeedlessRankResearch
open ContactFlagRankKernel6641Research
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
variable (K:Type*) [Field K]
abbrev LocalPoly:=MvPolynomial (Fin 3) K
abbrev Poly4:=MvPolynomial (Fin 4) K
abbrev CoefficientIndex (D w L s:ℕ):=
 (i:Fin (L+1)) × (j:Fin (s+1)) ×
   (Fin (min 1 (L+1-i.val-j.val)) ×
     Fin (D-w*i.val-(w-1)*j.val))
def columnExponent {D w L s:ℕ}
   (c:CoefficientIndex D w L s):Fin 4 →₀ ℕ:=
 Finsupp.single 0 c.2.2.2.val+Finsupp.single 1 c.1.val+
   Finsupp.single 2 c.2.1.val
@[simp] theorem columnExponent_x {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 0=c.2.2.2.val:=by
 simp [columnExponent]
@[simp] theorem columnExponent_y {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 1=c.1.val:=by
 simp [columnExponent]
@[simp] theorem columnExponent_r {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 2=c.2.1.val:=by
 simp [columnExponent]
@[simp] theorem columnExponent_z {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 3=0:=by
 simp [columnExponent]
theorem columnExponent_injective (D w L s:ℕ):
   Function.Injective
     (columnExponent (D:=D) (w:=w) (L:=L) (s:=s)):=by
 intro c d h
 have hx:=congrArg (fun e:Fin 4 →₀ ℕ => e 0) h
 have hy:=congrArg (fun e:Fin 4 →₀ ℕ => e 1) h
 have hr:=congrArg (fun e:Fin 4 →₀ ℕ => e 2) h
 rcases c with ⟨⟨ci,hci⟩,⟨⟨cj,hcj⟩,⟨⟨cz,hcz⟩,⟨ce,hce⟩⟩⟩⟩
 rcases d with ⟨⟨di,hdi⟩,⟨⟨dj,hdj⟩,⟨⟨dz,hdz⟩,⟨de,hde⟩⟩⟩⟩
 simp only [columnExponent_x] at hx
 simp only [columnExponent_y] at hy
 simp only [columnExponent_r] at hr
 subst di
 subst dj
 subst de
 have hcz0:cz=0:=by omega
 have hdz0:dz=0:=by omega
 subst cz
 subst dz
 rfl
def globalExponents (D w L s:ℕ):Set (Fin 4 →₀ ℕ):=
 {d | d 1+d 2 ≤ L∧d 2 ≤ s∧d 3=0∧
   d 0+w*d 1+(w-1)*d 2 < D}
def globalCoefficientBox (D w L s:ℕ):Submodule K (Poly4 K):=
 MvPolynomial.restrictSupport K (globalExponents D w L s)
theorem columnMonomial_mem (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a∈
     globalCoefficientBox K D w L s:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 have hi:=c.1.isLt
 have hj:=c.2.1.isLt
 have ht:=c.2.2.1.isLt
 have he:=c.2.2.2.isLt
 have htri:c.1.val+c.2.1.val ≤ L:=by
   have hminpos:0 < min 1 (L+1-c.1.val-c.2.1.val):=by
     omega
   have hpos:0 < L+1-c.1.val-c.2.1.val:=
     hminpos.trans_le (min_le_right _ _)
   omega
 unfold globalExponents
 simp only [Set.mem_setOf_eq,columnExponent_x,columnExponent_y,
   columnExponent_r,columnExponent_z]
 exact ⟨htri,by omega,by simp,by omega⟩
def reconstruct (D w L s:ℕ) (theta:CoefficientIndex D w L s → K):
   Poly4 K:=
 ∑ c:CoefficientIndex D w L s,
   MvPolynomial.monomial (columnExponent c) (theta c)
theorem reconstruct_coeff (D w L s:ℕ)
   (theta:CoefficientIndex D w L s → K) (c:CoefficientIndex D w L s):
   MvPolynomial.coeff (columnExponent c) (reconstruct K D w L s theta)=
     theta c:=by
 classical
 simp [reconstruct,MvPolynomial.coeff_sum,
   (columnExponent_injective D w L s).eq_iff]
@[simp] theorem reconstruct_zero (D w L s:ℕ):
   reconstruct K D w L s (0:CoefficientIndex D w L s → K)=0:=by
 simp [reconstruct]
theorem reconstruct_injective (D w L s:ℕ):
   Function.Injective (reconstruct K D w L s):=by
 intro theta eta h
 funext c
 have hh:=congrArg (MvPolynomial.coeff (columnExponent c)) h
 simpa only [reconstruct_coeff] using hh
theorem reconstruct_ne_zero (D w L s:ℕ)
   (theta:CoefficientIndex D w L s → K) (htheta:theta≠0):
   reconstruct K D w L s theta≠0:=by
 intro hz
 apply htheta
 apply reconstruct_injective K D w L s
 simpa only [reconstruct_zero] using hz
theorem reconstruct_mem_box (D w L s:ℕ)
   (theta:CoefficientIndex D w L s → K):
   reconstruct K D w L s theta∈globalCoefficientBox K D w L s:=by
 classical
 unfold reconstruct
 apply Submodule.sum_mem
 intro c hc
 exact columnMonomial_mem K D w L s c (theta c)
def coefficientCount (D w L s:ℕ):ℕ:=
 ∑ i∈Finset.range (L+1),
   ∑ j∈Finset.range (s+1),
     min 1 (L+1-i-j)*(D-w*i-(w-1)*j)
theorem coefficient_index_card (D w L s:ℕ):
   Fintype.card (CoefficientIndex D w L s)=coefficientCount D w L s:=by
 simp [CoefficientIndex,coefficientCount,Fintype.card_sigma,
   Finset.sum_range]
def localMonomial (f j:ℕ):LocalPoly K:=
 MvPolynomial.monomial (Finsupp.single 0 f+Finsupp.single 1 j) 1
theorem localMonomial_mem (f j:ℕ):
   localMonomial K f j∈seedlessBox K f (f+j) j:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 simp [localMonomial,seedlessExponents]
def blockEntry (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (r:ℕ):LocalPoly K:=
 ∑ f:Fin (c.1.val+1),
   if f.val ≤ r then
     ((((c.2.2.2.val.choose (r-f.val):ℕ):K)*
       x^(c.2.2.2.val-(r-f.val))*
       ((c.1.val.choose f.val:ℕ):K)*u^(c.1.val-f.val))) •
         localMonomial K f.val c.2.1.val
   else 0
theorem blockEntry_mem (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   blockEntry K D w L s x u c r∈
     seedlessBox K (min r L) L s:=by
 classical
 unfold blockEntry
 apply Submodule.sum_mem
 intro f hf
 split_ifs with hfr
 · apply (seedlessBox K (min r L) L s).smul_mem
   apply MvPolynomial.restrictSupport_mono (R:=K) ?_
     (localMonomial_mem K f.val c.2.1.val)
   intro d hd
   rcases hd with ⟨hd0,hd01,hd1,hd2⟩
   have hi:=c.1.isLt
   have hj:=c.2.1.isLt
   have ht:=c.2.2.1.isLt
   have hfi:=f.isLt
   have htri:c.1.val+c.2.1.val ≤ L:=by
     have hminpos:0 < min 1 (L+1-c.1.val-c.2.1.val):=by
       omega
     have hpos:0 < L+1-c.1.val-c.2.1.val:=
       hminpos.trans_le (min_le_right _ _)
     omega
   exact ⟨hd0.trans (by omega),by omega,hd1.trans (by omega),hd2⟩
 · exact (seedlessBox K (min r L) L s).zero_mem
def boundedBlockEntry (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   seedlessBox K (min r L) L s:=
 ⟨blockEntry K D w L s x u c r,blockEntry_mem K D w L s x u c r⟩
def extractBlock (D w L s:ℕ) (x u:K) (r:ℕ):
   (CoefficientIndex D w L s → K) →ₗ[K]
     seedlessBox K (min r L) L s where
 toFun theta:=∑ c:CoefficientIndex D w L s,
   theta c • boundedBlockEntry K D w L s x u c r
 map_add' theta eta:=by
   simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
 map_smul' a theta:=by
   simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,
     RingHom.id_apply]
def localRankBound (m L s:ℕ):ℕ:=
 ∑ r∈Finset.range m,
   seedlessContactRankBound (min r L) L s (m-r)
abbrev LocalTarget (m L s:ℕ):=
 (r:Fin m) → LinearMap.range
   (seedlessBlockJet K (min r.val L) L s (m-r.val))
theorem localTarget_finrank_le (m L s:ℕ):
   Module.finrank K (LocalTarget K m L s) ≤ localRankBound m L s:=by
 change Module.finrank K ((r:Fin m) → LinearMap.range
   (seedlessBlockJet K (min r.val L) L s (m-r.val))) ≤ _
 rw [Module.finrank_pi_fintype]
 unfold localRankBound
 rw [Finset.sum_range]
 apply Finset.sum_le_sum
 intro r hr
 exact seedlessBlockJet_rank_le_contactRankBound K (min r.val L) L s
   (m-r.val) (min_le_right r.val L)
abbrev GlobalTarget (I:Type*) (m L s:ℕ):=I → LocalTarget K m L s
def constraintMap {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes received:I → K):
   (CoefficientIndex D w L s → K) →ₗ[K] GlobalTarget K I m L s:=
 LinearMap.pi fun i => LinearMap.pi fun r =>
   (seedlessBlockJet K (min r.val L) L s (m-r.val)).rangeRestrict.comp
     (extractBlock K D w L s (nodes i) (received i) r.val)
theorem exists_nonzero_kernel_array {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes received:I → K)
   (hgate:Fintype.card I*localRankBound m L s <
     coefficientCount D w L s):
   ∃ theta:CoefficientIndex D w L s → K,theta≠0∧
     constraintMap K D w L s m nodes received theta=0:=by
 classical
 by_contra hnone
 have hinj:Function.Injective
     (constraintMap K D w L s m nodes received):=by
   intro theta eta heq
   by_contra hne
   apply hnone
   refine ⟨theta-eta,sub_ne_zero.mpr hne,?_⟩
   rw [map_sub,heq,sub_self]
 have hdim:=LinearMap.finrank_le_finrank_of_injective hinj
 rw [Module.finrank_fintype_fun_eq_card,coefficient_index_card] at hdim
 have htarget:Module.finrank K (GlobalTarget K I m L s) ≤
     Fintype.card I*localRankBound m L s:=by
   change Module.finrank K (I → LocalTarget K m L s) ≤ _
   rw [Module.finrank_pi_fintype]
   calc
     (∑ _i:I,Module.finrank K (LocalTarget K m L s)) ≤
         ∑ _i:I,localRankBound m L s:=by
       apply Finset.sum_le_sum
       intro i hi
       exact localTarget_finrank_le K m L s
     _=Fintype.card I*localRankBound m L s:=by simp
 exact (Nat.not_le_of_gt hgate) (hdim.trans htarget)
theorem all_blocks_divisible_of_kernel {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes received:I → K)
   (theta:CoefficientIndex D w L s → K)
   (hzero:constraintMap K D w L s m nodes received theta=0):
   ∀ i:I,∀ r:ℕ,slopeDifference K^(m-r)∣
     ((extractBlock K D w L s (nodes i) (received i) r theta):LocalPoly K):=by
 intro i r
 by_cases hr:r < m
 · have hh:=congrArg
     (fun t:GlobalTarget K I m L s => ((t i ⟨r,hr⟩):LocalPoly K)) hzero
   change contactJet K (m-r)
     ((extractBlock K D w L s (nodes i) (received i) r theta):LocalPoly K)=0 at hh
   exact (contactJet_eq_zero_iff K (m-r) _).mp hh
 · have hm:m-r=0:=by omega
   simp only [hm,pow_zero,one_dvd]
def homogenizedTranslation (x u:K):
   Poly4 K →ₐ[K] Polynomial (LocalPoly K):=
 ContactFlagTranslation6641Research.homogenizedTranslation K x u 0
theorem columnMonomial_eq (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a=
     MvPolynomial.C a*MvPolynomial.X 0^c.2.2.2.val*
       MvPolynomial.X 1^c.1.val*MvPolynomial.X 2^c.2.1.val:=by
 rw [columnExponent,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single,
   ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem localMonomial_eq (f j:ℕ):
   localMonomial K f j=MvPolynomial.X 0^f*MvPolynomial.X 1^j:=by
 rw [localMonomial,MvPolynomial.monomial_add_single,
   ←MvPolynomial.X_pow_eq_monomial]
theorem translation_column_coeff (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (a:K) (r:ℕ):
   (homogenizedTranslation K x u
     (MvPolynomial.monomial (columnExponent c) a)).coeff r=
       a • blockEntry K D w L s x u c r:=by
 have hfactor:
     homogenizedTranslation K x u
         (MvPolynomial.monomial (columnExponent c) a)=
       Polynomial.C (MvPolynomial.C a)*
         (((Polynomial.X+Polynomial.C (MvPolynomial.C x))^c.2.2.2.val*
           (Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
             Polynomial.C (MvPolynomial.C u))^c.1.val*
           Polynomial.C (MvPolynomial.X 1^c.2.1.val))):=by
   rw [columnMonomial_eq K D w L s]
   simp [homogenizedTranslation,
     ContactFlagTranslation6641Research.homogenizedTranslation,
     ContactFlagTranslation6641Research.translationVariables,
     ContactFlagInterpolation6641Research.seedAffine,
     Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq]
   ring
 rw [hfactor,Polynomial.coeff_C_mul,
   ContactFlagTranslation6641Research.coeff_shifted_affine_product]
 unfold blockEntry
 rw [Finset.mul_sum,Finset.smul_sum]
 apply Finset.sum_congr rfl
 intro f hf
 split_ifs with hfr
 · simp only [localMonomial_eq,MvPolynomial.smul_eq_C_mul,map_mul,
     map_pow,map_natCast]
   ring
 · simp
theorem translation_reconstruct_coeff (D w L s:ℕ) (x u:K)
   (theta:CoefficientIndex D w L s → K) (r:ℕ):
   (homogenizedTranslation K x u (reconstruct K D w L s theta)).coeff r=
     ((extractBlock K D w L s x u r theta):LocalPoly K):=by
 rw [reconstruct,map_sum,Polynomial.finsetSum_coeff]
 simp only [translation_column_coeff]
 change (∑ c:CoefficientIndex D w L s,
     theta c • blockEntry K D w L s x u c r)=
   (((∑ c:CoefficientIndex D w L s,
     theta c • boundedBlockEntry K D w L s x u c r):
       seedlessBox K (min r L) L s):LocalPoly K)
 simp [boundedBlockEntry]
def n:ℕ:=262144
def errors:ℕ:=79866
def agreements:ℕ:=n-errors
def w:ℕ:=131071
def multiplicity:ℕ:=37
def yTotalCap:ℕ:=51
def slopeCap:ℕ:=9
def weightedCap:ℕ:=multiplicity*agreements
theorem parameter_values:
   agreements=182278∧weightedCap=6744286:=by
 norm_num [agreements,weightedCap,multiplicity,n,errors]
theorem coefficient_count_exact:
   coefficientCount weightedCap w yTotalCap slopeCap=1481264965:=by
 decide
theorem local_rank_exact:
   localRankBound multiplicity yTotalCap slopeCap=5650:=by
 decide
theorem nullity_exact:
   coefficientCount weightedCap w yTotalCap slopeCap-
     n*localRankBound multiplicity yTotalCap slopeCap=151365:=by
 rw [coefficient_count_exact,local_rank_exact]
 norm_num [n]
theorem interpolation_gate:
   n*localRankBound multiplicity yTotalCap slopeCap <
     coefficientCount weightedCap w yTotalCap slopeCap:=by
 rw [coefficient_count_exact,local_rank_exact]
 norm_num [n]
theorem exists_frozen_seedless_interpolant
   (received:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap∧
     ∀ (i:IRSProfile.Index) (r:ℕ),
       slopeDifference IRSProfile.Field^(multiplicity-r)∣
         (ContactTranslation.homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (received i) 0 Q).coeff r:=by
 obtain ⟨theta,htheta,hzero⟩:=exists_nonzero_kernel_array
   IRSProfile.Field weightedCap w yTotalCap slopeCap multiplicity
   IRSProfile.domain received (by
     rw [show Fintype.card IRSProfile.Index=n by
       norm_num [IRSProfile.Index,n]]
     exact interpolation_gate)
 refine ⟨reconstruct IRSProfile.Field weightedCap w yTotalCap slopeCap theta,
   reconstruct_ne_zero IRSProfile.Field _ _ _ _ theta htheta,
   reconstruct_mem_box IRSProfile.Field _ _ _ _ theta,?_⟩
 intro i r
 have hdiv:=all_blocks_divisible_of_kernel IRSProfile.Field
   weightedCap w yTotalCap slopeCap multiplicity IRSProfile.domain received
   theta hzero i r
 rw [←translation_reconstruct_coeff IRSProfile.Field weightedCap w
   yTotalCap slopeCap (IRSProfile.domain i) (received i) theta r] at hdiv
 exact hdiv
theorem seedlessBox_le_legacy:
   globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ≤
     ContactInterpolation.globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap:=by
 apply MvPolynomial.restrictSupport_mono
 intro d hd
 rcases hd with ⟨hYR,hR,hZ,hweighted⟩
 exact ⟨by omega,hR,hweighted⟩
theorem exists_frozen_seedless_vanishing_interpolant
   (received:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap∧
     Q∈ContactInterpolation.globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap∧
     ∀ (P:Polynomial IRSProfile.Field)
       (support:Finset IRSProfile.Index),
       P.natDegree ≤ w → agreements ≤ support.card →
       (∀ i∈support,P.eval (IRSProfile.domain i)=received i) →
       ContactTranslation.specialization IRSProfile.Field P 0 Q=0:=by
 classical
 obtain ⟨Q,hQ,hbox,hcontact⟩:=
   exists_frozen_seedless_interpolant received
 have hlegacy:=seedlessBox_le_legacy hbox
 refine ⟨Q,hQ,hbox,hlegacy,?_⟩
 intro P support hdegree hcard hvalues
 apply ContactTranslation.specialization_eq_zero_of_contact_and_degree
   IRSProfile.Field Q P 0 IRSProfile.domain received (fun _ => 0)
     support multiplicity
 · intro i hi r
   exact hcontact i r
 · intro i hi
   simpa only [mul_zero,add_zero] using hvalues i hi
 · have hdeg:=ContactTranslation.specialization_natDegree_lt
     IRSProfile.Field weightedCap w yTotalCap slopeCap Q P 0
     (by norm_num [weightedCap,multiplicity,agreements,n,errors])
     hlegacy hdegree
   have hbound:weightedCap ≤ multiplicity*support.card:=by
     rw [weightedCap]
     exact Nat.mul_le_mul_left multiplicity hcard
   exact hdeg.trans_le hbound
end
end ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch
