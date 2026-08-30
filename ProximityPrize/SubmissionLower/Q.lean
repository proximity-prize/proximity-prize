import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.N4
import ProximityPrize.SubmissionLower.Y2
namespace ProximityPrize.SubmissionLower.RCN174
open RCN256
open ProximityPrize.Benchmark
open scoped BigOperators
noncomputable section
variable (K:Type*) [Field K]
theorem coefficientBox_mono {M L s M' L' s':ℕ}
   (hM:M ≤ M') (hL:L ≤ L') (hs:s ≤ s'):
   coefficientBox K M L s ≤ coefficientBox K M' L' s':=by
 apply MvPolynomial.restrictSupport_mono
 intro d hd
 exact ⟨hd.1.trans hM,hd.2.1.trans hL,hd.2.2.trans hs⟩
def localMonomial (f j z:ℕ):Poly K:=
 MvPolynomial.monomial
   (Finsupp.single 0 f+Finsupp.single 1 j+Finsupp.single 2 z) 1
theorem localMonomial_mem (f j z:ℕ):
   localMonomial K f j z∈coefficientBox K f (f+z) j:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 simp [boxExponents]
def seedAffine (u₀ u₁:K):Poly K:=
 MvPolynomial.C u₀+MvPolynomial.monomial (Finsupp.single 2 1) u₁
theorem seedAffine_mem (u₀ u₁:K):
   seedAffine K u₀ u₁∈coefficientBox K 0 1 0:=by
 apply (coefficientBox K 0 1 0).add_mem
 · change MvPolynomial.monomial 0 u₀∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
 · apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [boxExponents]
theorem seedAffine_pow_mem (u₀ u₁:K) (t:ℕ):
   seedAffine K u₀ u₁^t∈coefficientBox K 0 t 0:=by
 induction t with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [boxExponents]
 | succ t ih =>
     simpa only [pow_succ,Nat.zero_add] using
       coefficientBox_mul K ih (seedAffine_mem K u₀ u₁)
abbrev CoefficientIndex (D w L s:ℕ):=
 (i:Fin (L+1)) × (j:Fin (s+1)) ×
   (Fin (L+1-i.val) × Fin (D-w*i.val-(w-1)*j.val))
def columnExponent {D w L s:ℕ} (c:CoefficientIndex D w L s):Fin 4 →₀ ℕ:=
 Finsupp.single 0 c.2.2.2.val+Finsupp.single 1 c.1.val+
   Finsupp.single 2 c.2.1.val+Finsupp.single 3 c.2.2.1.val
@[simp] theorem columnExponent_x {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 0=c.2.2.2.val:=by simp [columnExponent]
@[simp] theorem columnExponent_y {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 1=c.1.val:=by simp [columnExponent]
@[simp] theorem columnExponent_r {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 2=c.2.1.val:=by simp [columnExponent]
@[simp] theorem columnExponent_z {D w L s:ℕ} (c:CoefficientIndex D w L s):
   columnExponent c 3=c.2.2.1.val:=by simp [columnExponent]
theorem columnExponent_injective (D w L s:ℕ):
   Function.Injective (columnExponent (D:=D) (w:=w) (L:=L) (s:=s)):=by
 intro c d h
 have hx:=congrArg (fun e:Fin 4 →₀ ℕ => e 0) h
 have hy:=congrArg (fun e:Fin 4 →₀ ℕ => e 1) h
 have hr:=congrArg (fun e:Fin 4 →₀ ℕ => e 2) h
 have hz:=congrArg (fun e:Fin 4 →₀ ℕ => e 3) h
 rcases c with ⟨⟨ci,hci⟩,⟨⟨cj,hcj⟩,⟨⟨cz,hcz⟩,⟨ce,hce⟩⟩⟩⟩
 rcases d with ⟨⟨di,hdi⟩,⟨⟨dj,hdj⟩,⟨⟨dz,hdz⟩,⟨de,hde⟩⟩⟩⟩
 simp only [columnExponent_x] at hx
 simp only [columnExponent_y] at hy
 simp only [columnExponent_r] at hr
 simp only [columnExponent_z] at hz
 subst di
 subst dj
 subst dz
 subst de
 rfl
def globalExponents (D w L s:ℕ):Set (Fin 4 →₀ ℕ):=
 {d | d 1+d 3 ≤ L∧d 2 ≤ s∧
   d 0+w*d 1+(w-1)*d 2 < D}
def globalCoefficientBox (D w L s:ℕ):
   Submodule K (MvPolynomial (Fin 4) K):=
 MvPolynomial.restrictSupport K (globalExponents D w L s)
theorem columnMonomial_mem (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a∈
     globalCoefficientBox K D w L s:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 have hi:=c.1.isLt
 have hj:=c.2.1.isLt
 have hz:=c.2.2.1.isLt
 have he:=c.2.2.2.isLt
 simp only [globalExponents,Set.mem_setOf_eq,columnExponent_x,
   columnExponent_y,columnExponent_r,columnExponent_z]
 omega
def reconstruct (D w L s:ℕ) (θ:CoefficientIndex D w L s → K):
   MvPolynomial (Fin 4) K:=
 ∑ c:CoefficientIndex D w L s,
   MvPolynomial.monomial (columnExponent c) (θ c)
theorem reconstruct_coeff (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K) (c:CoefficientIndex D w L s):
   MvPolynomial.coeff (columnExponent c) (reconstruct K D w L s θ)=θ c:=by
 classical
 simp [reconstruct,MvPolynomial.coeff_sum,
   (columnExponent_injective D w L s).eq_iff]
@[simp] theorem reconstruct_zero (D w L s:ℕ):
   reconstruct K D w L s (0:CoefficientIndex D w L s → K)=0:=by
 simp [reconstruct]
theorem reconstruct_injective (D w L s:ℕ):
   Function.Injective (reconstruct K D w L s):=by
 intro θ η h
 funext c
 have hh:=congrArg (MvPolynomial.coeff (columnExponent c)) h
 simpa only [reconstruct_coeff] using hh
theorem reconstruct_ne_zero (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K) (hθ:θ≠0):
   reconstruct K D w L s θ≠0:=by
 intro hzero
 apply hθ
 apply reconstruct_injective K D w L s
 simpa only [reconstruct_zero] using hzero
theorem reconstruct_mem_globalCoefficientBox (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K):
   reconstruct K D w L s θ∈globalCoefficientBox K D w L s:=by
 classical
 unfold reconstruct
 apply Submodule.sum_mem
 intro c hc
 exact columnMonomial_mem K D w L s c (θ c)
theorem reconstruct_support_caps (D w L s:ℕ)
   (θ:CoefficientIndex D w L s → K):
   ∀ d∈(reconstruct K D w L s θ).support,
     d 1+d 3 ≤ L∧d 2 ≤ s∧d 0+w*d 1+(w-1)*d 2 < D:=
 reconstruct_mem_globalCoefficientBox K D w L s θ
def coefficientCount (D w L s:ℕ):ℕ:=
 ∑ i∈Finset.range (L+1),
   ∑ j∈Finset.range (s+1),
     (L+1-i)*(D-w*i-(w-1)*j)
theorem coefficient_index_card (D w L s:ℕ):
   Fintype.card (CoefficientIndex D w L s)=coefficientCount D w L s:=by
 simp [CoefficientIndex,coefficientCount,Fintype.card_sigma,Finset.sum_range]
def blockEntry (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):Poly K:=
 ∑ f:Fin (c.1.val+1),
   if f.val ≤ r then
     (((c.2.2.2.val.choose (r-f.val):ℕ):K)*
       x^(c.2.2.2.val-(r-f.val))*
       ((c.1.val.choose f.val:ℕ):K)) •
         (seedAffine K u₀ u₁^(c.1.val-f.val)*
           localMonomial K f.val c.2.1.val c.2.2.1.val)
   else 0
theorem blockEntry_mem (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   blockEntry K D w L s x u₀ u₁ c r∈
     coefficientBox K (min r L) L s:=by
 classical
 unfold blockEntry
 apply Submodule.sum_mem
 intro f hf
 split_ifs with hfr
 · apply (coefficientBox K (min r L) L s).smul_mem
   have hi:=c.1.isLt
   have hj:=c.2.1.isLt
   have hz:=c.2.2.1.isLt
   have hfi:=f.isLt
   have hmul:=coefficientBox_mul K
     (seedAffine_pow_mem K u₀ u₁ (c.1.val-f.val))
     (localMonomial_mem K f.val c.2.1.val c.2.2.1.val)
   apply coefficientBox_mono K (show 0+f.val ≤ min r L by omega)
     (show c.1.val-f.val+(f.val+c.2.2.1.val) ≤ L by omega)
     (show 0+c.2.1.val ≤ s by omega)
   exact hmul
 · exact (coefficientBox K (min r L) L s).zero_mem
def boundedBlockEntry (D w L s:ℕ) (x u₀ u₁:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   coefficientBox K (min r L) L s:=
 ⟨blockEntry K D w L s x u₀ u₁ c r,
   blockEntry_mem K D w L s x u₀ u₁ c r⟩
def extractBlock (D w L s:ℕ) (x u₀ u₁:K) (r:ℕ):
   (CoefficientIndex D w L s → K) →ₗ[K]
     coefficientBox K (min r L) L s where
 toFun θ:=∑ c:CoefficientIndex D w L s,
   θ c • boundedBlockEntry K D w L s x u₀ u₁ c r
 map_add' θ η:=by
   simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
 map_smul' a θ:=by
   simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,RingHom.id_apply]
theorem full_contactRankBound_eq (r m L s:ℕ):
   contactRankBound (min r L) L s (m-r)=
     contactRankBound (min r L) L s (min (r+1) (m-r)):=by
 by_cases h:r+1 ≤ m-r
 · have hM:min r L ≤ r:=min_le_left r L
   have hzero:min r L+1-(m-r)=0:=by omega
   have hzero':min r L+1-(r+1)=0:=by omega
   simp only [Nat.min_eq_left h,contactRankBound,blockKernelLowerBound,
     hzero,hzero',Finset.range_zero,Finset.sum_empty,mul_zero,Nat.sub_zero]
 · have h':m-r ≤ r+1:=by omega
   rw [Nat.min_eq_right h']
abbrev LocalTarget (m L s:ℕ):=
 (r:Fin m) → LinearMap.range
   (blockJet K (min r.val L) L s (m-r.val))
theorem localTarget_finrank_le (m L s:ℕ):
   Module.finrank K (LocalTarget K m L s) ≤ localRankBound m L s:=by
 change Module.finrank K ((r:Fin m) → LinearMap.range
   (blockJet K (min r.val L) L s (m-r.val))) ≤ _
 rw [Module.finrank_pi_fintype]
 unfold localRankBound
 rw [Finset.sum_range]
 apply Finset.sum_le_sum
 intro r hr
 have hh:=blockJet_rank_le_contactRankBound K (min r.val L) L s (m-r.val)
   (min_le_right r.val L)
 rw [full_contactRankBound_eq] at hh
 exact hh
abbrev GlobalTarget (I:Type*) (m L s:ℕ):=I → LocalTarget K m L s
theorem globalTarget_finrank_le {I:Type*} [Fintype I] (m L s:ℕ):
   Module.finrank K (GlobalTarget K I m L s) ≤
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
def constraintMap {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K):
   (CoefficientIndex D w L s → K) →ₗ[K] GlobalTarget K I m L s:=
 LinearMap.pi fun i => LinearMap.pi fun r =>
   (blockJet K (min r.val L) L s (m-r.val)).rangeRestrict.comp
     (extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val)
theorem constraintMap_apply {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (θ:CoefficientIndex D w L s → K) (i:I) (r:Fin m):
   ((constraintMap K D w L s m nodes u₀ u₁ θ i r):Poly K)=
     contactJet K (m-r.val)
       ((extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ):Poly K):=rfl
theorem exists_nonzero_kernel_array {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (hgate:Fintype.card I*localRankBound m L s < coefficientCount D w L s):
   ∃ θ:CoefficientIndex D w L s → K,
     θ≠0∧constraintMap K D w L s m nodes u₀ u₁ θ=0:=by
 classical
 by_contra hnone
 have hinj:Function.Injective (constraintMap K D w L s m nodes u₀ u₁):=by
   intro θ η heq
   by_contra hne
   apply hnone
   refine ⟨θ-η,sub_ne_zero.mpr hne,?_⟩
   rw [map_sub,heq,sub_self]
 have hdim:=LinearMap.finrank_le_finrank_of_injective hinj
 rw [Module.finrank_fintype_fun_eq_card,coefficient_index_card] at hdim
 have hupper:=globalTarget_finrank_le K (I:=I) m L s
 exact (Nat.not_le_of_gt hgate) (hdim.trans hupper)
theorem exists_nonzero_block_equations {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u₀ u₁:I → K)
   (hgate:Fintype.card I*localRankBound m L s < coefficientCount D w L s):
   ∃ θ:CoefficientIndex D w L s → K,θ≠0∧
     ∀ (i:I) (r:Fin m),
       contactJet K (m-r.val)
         ((extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ):Poly K)=0:=by
 obtain ⟨θ,hθ,hzero⟩:=exists_nonzero_kernel_array K D w L s m nodes u₀ u₁ hgate
 refine ⟨θ,hθ,?_⟩
 intro i r
 have hh:=congrArg (fun t:GlobalTarget K I m L s => ((t i r):Poly K)) hzero
 change contactJet K (m-r.val)
   ((extractBlock K D w L s (nodes i) (u₀ i) (u₁ i) r.val θ):Poly K)=0 at hh
 exact hh
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
abbrev FrozenCoefficientIndex:=CoefficientIndex 3324960 131071 176 5
theorem exists_frozen_nonzero_contact_array
   (u₀ u₁:IRSProfile.Index → IRSProfile.Field):
   ∃ θ:FrozenCoefficientIndex → IRSProfile.Field,θ≠0∧
     ∀ (i:IRSProfile.Index) (r:Fin 18),
       contactJet IRSProfile.Field (18-r.val)
         ((extractBlock IRSProfile.Field 3324960 131071 176 5
           (IRSProfile.domain i) (u₀ i) (u₁ i) r.val θ):Poly IRSProfile.Field)=0:=by
 apply exists_nonzero_block_equations IRSProfile.Field 3324960 131071 176 5 18
   (fun i:IRSProfile.Index => IRSProfile.domain i) u₀ u₁
 rw [show Fintype.card IRSProfile.Index=262144 by norm_num [IRSProfile.Index]]
 exact RCN051.interpolation_gate
theorem exists_frozen_nonzero_polynomial_and_equations
   (u₀ u₁:IRSProfile.Index → IRSProfile.Field):
   ∃ (Q:MvPolynomial (Fin 4) IRSProfile.Field)
     (θ:FrozenCoefficientIndex → IRSProfile.Field),
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field 3324960 131071 176 5∧
     Q=reconstruct IRSProfile.Field 3324960 131071 176 5 θ∧
     ∀ (i:IRSProfile.Index) (r:Fin 18),
       contactJet IRSProfile.Field (18-r.val)
         ((extractBlock IRSProfile.Field 3324960 131071 176 5
           (IRSProfile.domain i) (u₀ i) (u₁ i) r.val θ):Poly IRSProfile.Field)=0:=by
 obtain ⟨θ,hθ,hconstraints⟩:=exists_frozen_nonzero_contact_array u₀ u₁
 exact ⟨reconstruct IRSProfile.Field 3324960 131071 176 5 θ,θ,
   reconstruct_ne_zero IRSProfile.Field 3324960 131071 176 5 θ hθ,
   reconstruct_mem_globalCoefficientBox IRSProfile.Field 3324960 131071 176 5 θ,
   rfl,hconstraints⟩
end
end ProximityPrize.SubmissionLower.RCN174
