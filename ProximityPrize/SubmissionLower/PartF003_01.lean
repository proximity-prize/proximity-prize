import ProximityPrize.SubmissionLower.PartF003_00
section Compact_PackedLegacyCore1
section PackedLegacy_N4
namespace ProximityPrize.SubmissionLower.RCN256
open scoped BigOperators Pointwise
noncomputable section
variable (K:Type*) [Field K]

theorem kernelEmbedding_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (kernelEmbedding K hM hL hs):=by
 intro q r heq
 apply multiplyIntoBox_injective K hM hL hs
 exact congrArg Subtype.val heq
theorem blockJet_rank_add_quotient_finrank_le {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Module.finrank K (LinearMap.range (blockJet K M L s h))+
       Module.finrank K (coefficientBox K (M-h) (L-h) (s-h)) ≤
     Module.finrank K (coefficientBox K M L s):=by
 have hker:=LinearMap.finrank_le_finrank_of_injective
   (kernelEmbedding_injective K hM hL hs)
 have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
 omega
theorem blockJet_rank_le_triangle_difference {M L s h:ℕ}
   (hML:M ≤ L) (hM:h ≤ M) (hs:h ≤ s):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     (s+1)*(∑ i:Fin (M+1),(L-i.val+1))-
       (s-h+1)*(∑ i:Fin (M-h+1),(L-h-i.val+1)):=by
 have hineq:=blockJet_rank_add_quotient_finrank_le K hM (hM.trans hML) hs
 rw [coefficientBox_finrank_of_le K M L s hML,
   coefficientBox_finrank_of_le K (M-h) (L-h) (s-h)
     (Nat.sub_le_sub_right hML h)] at hineq
 omega
theorem blockJet_rank_le_input (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     (s+1)*∑ i:Fin (M+1),(L-i.val+1):=by
 have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
 rw [coefficientBox_finrank_of_le K M L s hML] at hsum
 omega
theorem coefficientBox_finrank_range (M L s:ℕ) (hML:M ≤ L):
   Module.finrank K (coefficientBox K M L s)=
     (s+1)*∑ i∈Finset.range (M+1),(L+1-i):=by
 rw [coefficientBox_finrank_of_le K M L s hML]
 congr 1
 rw [Finset.sum_range]
 apply Finset.sum_congr rfl
 intro i hi
 have hiM:=i.isLt
 omega
def blockInputCount (M L s:ℕ):ℕ:=
 (s+1)*∑ i∈Finset.range (M+1),(L+1-i)
def blockKernelLowerBound (M L s h:ℕ):ℕ:=
 (s+1-h)*
   ∑ i∈Finset.range (M+1-h),(L+1-h-i)
def contactRankBound (M L s h:ℕ):ℕ:=
 blockInputCount M L s-blockKernelLowerBound M L s h
theorem blockJet_rank_le_contactRankBound (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (blockJet K M L s h)) ≤
     contactRankBound M L s h:=by
 by_cases hM:h ≤ M
 · by_cases hs:h ≤ s
   · have hL:h ≤ L:=hM.trans hML
     have hineq:=blockJet_rank_add_quotient_finrank_le K hM hL hs
     rw [coefficientBox_finrank_range K M L s hML,
       coefficientBox_finrank_range K (M-h) (L-h) (s-h)
         (Nat.sub_le_sub_right hML h)] at hineq
     have hMeq:M-h+1=M+1-h:=by omega
     have hLeq:L-h+1=L+1-h:=by omega
     have hseq:s-h+1=s+1-h:=by omega
     rw [hMeq,hLeq,hseq] at hineq
     unfold contactRankBound blockInputCount blockKernelLowerBound
     omega
   · have hzero:s+1-h=0:=by omega
     have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
     rw [coefficientBox_finrank_range K M L s hML] at hsum
     simp only [contactRankBound,blockKernelLowerBound,hzero,zero_mul,Nat.sub_zero,
       blockInputCount]
     omega
 · have hzero:M+1-h=0:=by omega
   have hsum:=(blockJet K M L s h).finrank_range_add_finrank_ker
   rw [coefficientBox_finrank_range K M L s hML] at hsum
   simp only [contactRankBound,blockKernelLowerBound,hzero,Finset.range_zero,
     Finset.sum_empty,mul_zero,Nat.sub_zero,blockInputCount]
   omega
def localRankBound (m L s:ℕ):ℕ:=
 ∑ r∈Finset.range m,
   contactRankBound (min r L) L s (min (r+1) (m-r))
theorem sum_blockJet_ranks_le_localRankBound (m L s:ℕ):
   (∑ r∈Finset.range m,
     Module.finrank K (LinearMap.range
       (blockJet K (min r L) L s (min (r+1) (m-r))))) ≤
     localRankBound m L s:=by
 apply Finset.sum_le_sum
 intro r hr
 exact blockJet_rank_le_contactRankBound K (min r L) L s
   (min (r+1) (m-r)) (min_le_right r L)
end
end ProximityPrize.SubmissionLower.RCN256
end PackedLegacy_N4

/-! Packed from ProximityPrize.SubmissionLower.Y2. -/
section PackedLegacy_Y2
namespace ProximityPrize.SubmissionLower.RCN051
open Finset
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def n:ℕ:=262144
def w:ℕ:=131071
def agreements:ℕ:=184720
def prime:ℕ:=2130706433
def errors:ℕ:=n-agreements
def alignmentBudget:ℕ:=100000000000000000
def multiplicity:ℕ:=18
def seedTotalCap:ℕ:=176
def slopeCap:ℕ:=5
def weightedCap:ℕ:=multiplicity*agreements
def yCap:ℕ:=(weightedCap-1)/w
def gap:ℕ:=agreements-w
def algebraicCap:ℕ:=(2*slopeCap-1)*seedTotalCap
def coefficientCount:ℕ:=
 ∑ i∈range (seedTotalCap+1),
   ∑ j∈range (slopeCap+1),
     (seedTotalCap+1-i)*(weightedCap-w*i-(w-1)*j)
def contactExponent (r:ℕ):ℕ:=min (r+1) (multiplicity-r)
def localContactRank:ℕ:=
 ∑ r∈range multiplicity,
   (((slopeCap+1)*
       (∑ f∈range (min r seedTotalCap+1),(seedTotalCap+1-f)))-
     ((slopeCap+1-contactExponent r)*
       (∑ f∈range (min r seedTotalCap+1-contactExponent r),
         (seedTotalCap+1-contactExponent r-f))))
structure DegreeVector where
 y:ℕ
 r:ℕ
 z:ℕ
 deriving DecidableEq
def mixed (a b c:DegreeVector):ℕ:=
 a.y*b.r*c.z+a.y*b.z*c.r+
 a.r*b.y*c.z+a.r*b.z*c.y+
 a.z*b.y*c.r+a.z*b.r*c.y
def unitY:DegreeVector:=⟨1,0,0⟩
def unitR:DegreeVector:=⟨0,1,0⟩
def unitZ:DegreeVector:=⟨0,0,1⟩
def tailVector (h:ℕ):DegreeVector:=
 ⟨1+h*(2*yCap-1),h*(2*slopeCap-1),2*h*seedTotalCap⟩
def firstTail:DegreeVector:=tailVector (w+1)
def lastTail:DegreeVector:=tailVector weightedCap
def agreementVector:DegreeVector:=
 ⟨1+w*(2*yCap-1),w*(2*slopeCap-1),2*w*seedTotalCap+1⟩
def cutNumerator (v:DegreeVector):ℕ:=
 gap^2*mixed v firstTail lastTail+
 n*gap*mixed v firstTail agreementVector+
 (errors+1)*gap^2*mixed v firstTail unitZ
def wholeNumerator (v:DegreeVector):ℕ:=
 (n-w)^2*mixed v agreementVector agreementVector+
 (errors+1)*(n-w)*gap*mixed v agreementVector unitZ
def regularNumerator:ℕ:=
 yCap*wholeNumerator unitY+
 slopeCap*wholeNumerator unitR+
 seedTotalCap*wholeNumerator unitZ
def singularNumerator:ℕ:=
 gap*(algebraicCap+2*algebraicCap^2+
     algebraicCap*(1+2*(w+1)*(algebraicCap-1))+
     (errors+1)*algebraicCap)+
   n*algebraicCap*(1+2*w*(algebraicCap-1))
def totalNumerator:ℕ:=regularNumerator+gap*singularNumerator
theorem parameter_values:
   weightedCap=3324960∧yCap=25∧gap=53649∧
   errors=77424∧algebraicCap=1584:=by
 norm_num [weightedCap,multiplicity,agreements,yCap,w,gap,errors,
   n,algebraicCap,slopeCap,seedTotalCap]
theorem coefficient_count_exact:coefficientCount=36613226930:=by
  change (∑ i ∈ Finset.range (26 + 151),
    ∑ j ∈ Finset.range 6,
      (177 - i) * (3324960 - 131071 * i - 131070 * j)) = 36613226930
  rw [Finset.sum_range_add _ 26 151]
  have hzero : (∑ i ∈ Finset.range 151,
      ∑ j ∈ Finset.range 6,
        (177 - (26 + i)) *
          (3324960 - 131071 * (26 + i) - 131070 * j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hz : 3324960 - 131071 * (26 + i) = 0 :=
      Nat.sub_eq_zero_of_le (by omega)
    simp only [hz, Nat.zero_sub, Nat.mul_zero]
  rw [hzero, Nat.add_zero]
  simp_rw [← KernelEval.sumRange_eq]
  decide
theorem contact_rank_exact:localContactRank=139668:=by
 unfold localContactRank
 simp_rw [← KernelEval.sumRange_eq]
 decide
theorem interpolation_gate:n*localContactRank < coefficientCount:=by
 rw [coefficient_count_exact,contact_rank_exact]
 norm_num [n]
theorem characteristic_gates:
   w < weightedCap∧(2*slopeCap-1)*weightedCap < prime∧
   algebraicCap < prime∧slopeCap < prime:=by
 norm_num [w,weightedCap,multiplicity,agreements,slopeCap,prime,
   algebraicCap,seedTotalCap]
end ProximityPrize.SubmissionLower.RCN051
end PackedLegacy_Y2

/-! Packed from ProximityPrize.SubmissionLower.Q. -/
section PackedLegacy_Q
namespace ProximityPrize.SubmissionLower.RCN174
open RCN256 ProximityPrize.Benchmark
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
end
end ProximityPrize.SubmissionLower.RCN174
end PackedLegacy_Q

/-! Packed from ProximityPrize.SubmissionLower.DC. -/
section PackedLegacy_DC
namespace ProximityPrize.SubmissionLower
namespace BCHKSSubstitutionVanish
noncomputable def specializeZ {F:Type*} [Field F]
   (Q:Polynomial (Polynomial (Polynomial F))) (z:F):
   Polynomial (Polynomial F):=
 Polynomial.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) Q
noncomputable def triEval {F:Type*} [Field F]
   (Q:Polynomial (Polynomial (Polynomial F))) (z:F) (P:Polynomial F):
   Polynomial F:=Polynomial.eval P (specializeZ Q z)
theorem mul_card_le_natDegree_of_rootMultiplicity
   {F ι:Type*} [Field F] [DecidableEq F] [DecidableEq ι]
   (R:Polynomial F) (ω:ι ↪ F) (A:Finset ι) (m:Nat)
   (hmult:∀ i∈A,m ≤ R.rootMultiplicity (ω i)):
   m*A.card ≤ R.natDegree:=by
 let xs:Finset F:=A.map ω
 have hselected:
     ∑ x∈xs,Multiset.count x R.roots ≤ R.roots.card:=by
   let all:=xs ∪ R.roots.toFinset
   calc
     ∑ x∈xs,Multiset.count x R.roots ≤
         ∑ x∈all,Multiset.count x R.roots:=
       Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
     _=∑ x∈R.roots.toFinset,Multiset.count x R.roots:=by
       symm
       apply Finset.sum_subset (Finset.subset_union_right)
       intro x hxall hxroots
       exact Multiset.count_eq_zero.mpr (by simpa using hxroots)
     _=R.roots.card:=Multiset.toFinset_sum_count_eq R.roots
 calc
   m*A.card=∑ i∈A,m:=by simp [Nat.mul_comm]
   _ ≤ ∑ i∈A,R.rootMultiplicity (ω i):=
     Finset.sum_le_sum fun i hi => hmult i hi
   _=∑ x∈xs,R.rootMultiplicity x:=by
     symm
     exact Finset.sum_map A ω (fun x => R.rootMultiplicity x)
   _=∑ x∈xs,Multiset.count x R.roots:=by
     apply Finset.sum_congr rfl
     intro x hx
     exact (Polynomial.count_roots R).symm
   _ ≤ R.roots.card:=hselected
   _ ≤ R.natDegree:=Polynomial.card_roots' R
end BCHKSSubstitutionVanish
end ProximityPrize.SubmissionLower
end PackedLegacy_DC

/-! Packed from ProximityPrize.SubmissionLower.C6. -/
section PackedLegacy_C6
namespace ProximityPrize.SubmissionLower.RCN185
open Polynomial
section LocalRing
variable {F:Type*} [CommRing F]
theorem shifted_power_dvd_iff_taylor_coeff_zero
   (P:F[X]) (x:F) (h:ℕ):
   (Polynomial.X-Polynomial.C x)^h∣P ↔
     ∀ j < h,(taylor x P).coeff j=0:=by
 have hshift:taylor x ((Polynomial.X-Polynomial.C x)^h)=
     (Polynomial.X:F[X])^h:=by
   rw [taylor_pow,map_sub,taylor_X,taylor_C,add_sub_cancel_right]
 have hdiv:=map_dvd_iff (taylorEquiv x)
   (a:=((Polynomial.X:F[X])-Polynomial.C x)^h) (b:=P)
 change taylor x ((Polynomial.X-Polynomial.C x)^h)∣taylor x P ↔
   (Polynomial.X-Polynomial.C x)^h∣P at hdiv
 rw [hshift] at hdiv
 exact hdiv.symm.trans (Polynomial.X_pow_dvd_iff (f:=taylor x P) (n:=h))
noncomputable def contactResidual (P:F[X]) (x:F):F[X]:=
 taylor x P-Polynomial.C (P.eval x)-
   Polynomial.X*taylor x P.derivative
theorem X_sq_dvd_contactResidual (P:F[X]) (x:F):
   (Polynomial.X:F[X])^2∣contactResidual P x:=by
 rw [X_pow_dvd_iff]
 intro j hj
 have hcases:j=0∨j=1:=by omega
 rcases hcases with rfl | rfl
 · simp [contactResidual]
 · simp [contactResidual,coeff_X_mul]
end LocalRing
section GlobalVanishing
variable {F I J:Type*} [Field F] [DecidableEq F] [DecidableEq I]
end GlobalVanishing
end ProximityPrize.SubmissionLower.RCN185
end PackedLegacy_C6

/-! Packed from ProximityPrize.SubmissionLower.K. -/
section PackedLegacy_K
namespace ProximityPrize.SubmissionLower.RCN319
open RCN256 RCN174 ProximityPrize.Benchmark
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
     d 1+d 3 ≤ L∧d 2 ≤ s∧d 0+w*d 1+(w-1)*d 2 < D:=hcaps
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
end ProximityPrize.SubmissionLower.RCN319
end PackedLegacy_K

/-! Packed from ProximityPrize.SubmissionLower.BJ. -/
section PackedLegacy_BJ
namespace ProximityPrize.SubmissionLower.RCN139
open RCN077 RCN269 RCN233 RCN347 RCN174 RCN319
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
variable {K L:Type*} [Field K] [Field L]
theorem derivative_taylor (r:L) (P:Polynomial L):
   (Polynomial.taylor r P).derivative=Polynomial.taylor r P.derivative:=by
 simp [Polynomial.taylor_apply,Polynomial.derivative_comp]
theorem taylor_reconstruction_eq_specialization
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L) (P:Polynomial L):
   Polynomial.taylor (-(v 0))
       (MvPolynomial.eval₂Hom (Polynomial.C.comp coefficients)
         (reconstructionSubstitution v P) F)=
     specialization L (Polynomial.taylor (-(v 0)) P) (v 3)
       (MvPolynomial.map coefficients F):=by
 have hhom:
     (Polynomial.taylorAlgHom (-(v 0))).toRingHom.comp
         (MvPolynomial.eval₂Hom (Polynomial.C.comp coefficients)
           (reconstructionSubstitution v P))=
       (specialization L (Polynomial.taylor (-(v 0)) P) (v 3)).toRingHom.comp
         (MvPolynomial.map coefficients):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,reconstructionSubstitution,specialization]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,reconstructionSubstitution,specialization,
         derivative_taylor]
 exact DFunLike.congr_fun hhom F
theorem map_mem_globalCoefficientBox
   (coefficients:K →+*L) (F:Poly4 K) (bound w seedCap slopeCap:ℕ)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap):
   MvPolynomial.map coefficients F∈globalCoefficientBox L bound w seedCap slopeCap:=by
 intro d hd
 exact hcaps (MvPolynomial.support_map_subset coefficients F hd)
noncomputable def globalPolynomial
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):Polynomial L:=
 Polynomial.taylor (-(v 0)) (reconstructedPolynomial coefficients F v hF hregular w)
theorem globalPolynomial_natDegree_le
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (globalPolynomial coefficients F v hF hregular w).natDegree ≤ w:=by
 simpa only [globalPolynomial,Polynomial.natDegree_taylor] using
   reconstructedPolynomial_natDegree_le coefficients F v hF hregular w
theorem globalPolynomial_eval
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ) (x:L):
   (globalPolynomial coefficients F v hF hregular w).eval x=
     (reconstructedPolynomial coefficients F v hF hregular w).eval (x-v 0):=by
 simp only [globalPolynomial,Polynomial.taylor_eval,sub_eq_add_neg]
theorem globalPolynomial_initial_value
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (globalPolynomial coefficients F v hF hregular w).eval (v 0)=v 1:=by
 rw [globalPolynomial_eval,sub_self, ←Polynomial.taylor_coeff_zero (0:L),
   Polynomial.taylor_zero]
 exact reconstructedPolynomial_coeff_zero coefficients F v hF hregular w
theorem globalPolynomial_initial_slope
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ) (hw:1 ≤ w):
   (globalPolynomial coefficients F v hF hregular w).derivative.eval (v 0)=v 2:=by
 rw [globalPolynomial,derivative_taylor,Polynomial.taylor_eval,add_neg_cancel]
 rw [←Polynomial.taylor_coeff_one (0:L),Polynomial.taylor_zero]
 exact reconstructedPolynomial_coeff_one coefficients F v hF hregular w hw
theorem reconstructedEquation_natDegree_lt
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (bound w seedCap slopeCap:ℕ) (hbound:0 < bound)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap):
   (reconstructedEquation coefficients F v hF hregular w).natDegree < bound:=by
 have hdeg:=specialization_natDegree_lt L bound w seedCap slopeCap
   (MvPolynomial.map coefficients F) (globalPolynomial coefficients F v hF hregular w)
   (v 3) hbound (map_mem_globalCoefficientBox coefficients F bound w seedCap slopeCap hcaps)
   (globalPolynomial_natDegree_le coefficients F v hF hregular w)
 have heq:=taylor_reconstruction_eq_specialization coefficients F v
   (reconstructedPolynomial coefficients F v hF hregular w)
 change Polynomial.taylor (-(v 0)) (reconstructedEquation coefficients F v hF hregular w)=
   specialization L (globalPolynomial coefficients F v hF hregular w) (v 3)
     (MvPolynomial.map coefficients F) at heq
 rw [←heq,Polynomial.natDegree_taylor] at hdeg
 exact hdeg
theorem global_polynomiality_of_all_tails
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients v
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w seedCap slopeCap:ℕ) [CharP L p] (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap)
   (htails:∀ j,w < j → j ≤ bound →
     jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F v hF hregular)
       (contactCoordinate K F (1:Fin 4)) j=0):
   specialization L (globalPolynomial coefficients F v hF hregular w) (v 3)
     (MvPolynomial.map coefficients F)=0:=by
 have hdegree:=reconstructedEquation_natDegree_lt coefficients F v hF hregular
   bound w seedCap slopeCap (by omega) hcaps
 have hzero:=polynomiality_of_all_tails coefficients F v hF hregular p bound w
   hw hshort hchar htails hdegree
 have heq:=taylor_reconstruction_eq_specialization coefficients F v
   (reconstructedPolynomial coefficients F v hF hregular w)
 change Polynomial.taylor (-(v 0)) (reconstructedEquation coefficients F v hF hregular w)=
   specialization L (globalPolynomial coefficients F v hF hregular w) (v 3)
     (MvPolynomial.map coefficients F) at heq
 rw [←heq,hzero,map_zero]
end
end ProximityPrize.SubmissionLower.RCN139
end PackedLegacy_BJ

/-! Packed from ProximityPrize.SubmissionLower.D9. -/
section PackedLegacy_D9
namespace ProximityPrize.SubmissionLower.RCN231
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN319 RCN347
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section PolynomialIdentities
variable (K:Type*) [Field K]
theorem derivative_specialization (P:Polynomial K) (γ:K) (Q:Poly4 K):
   (specialization K P γ Q).derivative=
     specialization K P γ (MvPolynomial.pderiv (0:Fin 4) Q)+
     P.derivative*specialization K P γ (MvPolynomial.pderiv (1:Fin 4) Q)+
     P.derivative.derivative*
       specialization K P γ (MvPolynomial.pderiv (2:Fin 4) Q):=by
 induction Q using MvPolynomial.induction_on with
 | C a => simp [specialization]
 | add Q S hQ hS =>
     simp only [map_add,hQ,hS]
     ring
 | mul_X Q i hQ =>
     simp only [MvPolynomial.pderiv_mul,map_add,map_mul,
       Polynomial.derivative_mul,hQ]
     fin_cases i <;> simp [specialization] <;> ring
theorem solution_slope_identity (F:Poly4 K) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ F=0):
   specialization K P γ (polyH K F)*P.derivative.derivative=
     specialization K P γ (polyG K F):=by
 have hchain:=derivative_specialization K P γ F
 rw [hsolution,Polynomial.derivative_zero] at hchain
 have hG:specialization K P γ (polyG K F)=
     -(specialization K P γ (MvPolynomial.pderiv (0:Fin 4) F)+
       P.derivative*specialization K P γ (MvPolynomial.pderiv (1:Fin 4) F)):=by
   simp [polyG,specialization]
 rw [hG]
 change specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)*
     P.derivative.derivative=_
 linear_combination-hchain
theorem specialization_numeratorStep
   (F M:Poly4 K) (P:Polynomial K) (γ:K) (b:ℕ)
   (hsolution:specialization K P γ F=0):
   specialization K P γ (numeratorStep K F b M)=
     specialization K P γ (polyH K F)^2*
       (specialization K P γ M).derivative-
     (2*b:Polynomial K)*specialization K P γ M*
       specialization K P γ (polyH K F)*
       (specialization K P γ (polyH K F)).derivative:=by
 simp only [numeratorStep,clearedStep,map_sub,map_add,map_mul,
   map_pow,map_natCast]
 have hR:specialization K P γ (MvPolynomial.X (2:Fin 4))=P.derivative:=by
   simp [specialization]
 rw [hR, ←solution_slope_identity K F P γ hsolution,
   derivative_specialization K P γ M,
   derivative_specialization K P γ (polyH K F)]
 push_cast
 ring
theorem derivative_power_cancellation (H A:Polynomial K) (n:ℕ):
   H^2*(H^n*A).derivative-
     (n:Polynomial K)*(H^n*A)*H*H.derivative=
     H^(n+2)*A.derivative:=by
 cases n with
 | zero => simp [pow_two]
 | succ n =>
     rw [Polynomial.derivative_mul,Polynomial.derivative_pow_succ]
     simp only [Polynomial.C_add,Polynomial.C_1,Polynomial.C_eq_natCast,
       Nat.cast_add,Nat.cast_one,pow_succ]
     ring
theorem specialization_numerator_eq
   (F:Poly4 K) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ F=0) (b:ℕ):
   specialization K P γ (numerator K F b)=
     specialization K P γ (polyH K F)^(2*b)*Polynomial.derivative^[b] P:=by
 induction b with
 | zero => simp [numerator_zero,specialization]
 | succ b ih =>
     rw [numerator_succ,specialization_numeratorStep K F (numerator K F b) P γ b
       hsolution,ih]
     have hexp:2*(b+1)=2*b+2:=by omega
     rw [hexp,Function.iterate_succ_apply']
     simpa only [Nat.cast_mul,Nat.cast_ofNat] using
       derivative_power_cancellation K (specialization K P γ (polyH K F))
         (Polynomial.derivative^[b] P) (2*b)
theorem specialization_numerator_zero_of_degree
   (F:Poly4 K) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ F=0) (b:ℕ) (hb:P.natDegree < b):
   specialization K P γ (numerator K F b)=0:=by
 rw [specialization_numerator_eq K F P γ hsolution b,
   Polynomial.iterate_derivative_eq_zero hb,mul_zero]
end PolynomialIdentities
section ActualPoints
variable {K L:Type*} [Field K] [Field L]
def polynomialPoint (coefficients:K →+*L) (P:Polynomial K) (γ:K) (ξ:L):
   Fin 4 → L:=
 ![ξ,P.eval₂ coefficients ξ,P.derivative.eval₂ coefficients ξ,coefficients γ]
theorem eval_polynomialPoint_eq_specialization
   (coefficients:K →+*L) (P:Polynomial K) (γ:K) (ξ:L) (Q:Poly4 K):
   MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ) Q=
     (specialization K P γ Q).eval₂ coefficients ξ:=by
 have hhom:
     (Polynomial.eval₂RingHom coefficients ξ).comp (specialization K P γ).toRingHom=
       MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,specialization]
   · intro i
     fin_cases i <;> simp [RingHom.comp_apply,specialization,polynomialPoint]
 exact (DFunLike.congr_fun hhom Q).symm
theorem polynomialPoint_relation
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0):
   MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ) F=0:=by
 rw [eval_polynomialPoint_eq_specialization,hsolution]
 simp
theorem polynomialPoint_numerator_zero
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0) (b:ℕ) (hb:P.natDegree < b):
   MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (numerator K F b)=0:=by
 rw [eval_polynomialPoint_eq_specialization,
   specialization_numerator_zero_of_degree K F P γ hsolution b hb]
 simp
end ActualPoints
end
end ProximityPrize.SubmissionLower.RCN231
end PackedLegacy_D9

/-! Packed from ProximityPrize.SubmissionLower.T. -/
section PackedLegacy_T
namespace ProximityPrize.SubmissionLower.RCN229
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN231 RCN139 RCN319 RCN347
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
variable {K L:Type*} [Field K] [Field L]
theorem taylor_coeff_eq_derivative_div_factorial
   (P:Polynomial L) (ξ:L) (j:ℕ) (hfactorial:(j.factorial:L)≠0):
   (Polynomial.taylor ξ P).coeff j=
     (Polynomial.derivative^[j] P).eval ξ/(j.factorial:L):=by
 have hpoly:(j.factorial:Polynomial L)*Polynomial.hasseDeriv j P=
     Polynomial.derivative^[j] P:=by
   have h:=congrFun (Polynomial.factorial_smul_hasseDeriv (R:=L) j) P
   change j.factorial • (Polynomial.hasseDeriv j P)=
     Polynomial.derivative^[j] P at h
   simpa only [nsmul_eq_mul] using h
 have hvalue:=congrArg (Polynomial.evalRingHom ξ) hpoly
 simp only [map_mul,map_natCast] at hvalue
 change (j.factorial:L)*(Polynomial.hasseDeriv j P).eval ξ=
   (Polynomial.derivative^[j] P).eval ξ at hvalue
 rw [Polynomial.taylor_coeff]
 apply (eq_div_iff hfactorial).mpr
 simpa only [mul_comm] using hvalue
theorem polynomialPoint_jetCoefficient_eq
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (j:ℕ):
   jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F (polynomialPoint coefficients P γ ξ)
         (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular)
       (contactCoordinate K F (1:Fin 4)) j=
     (Polynomial.derivative^[j] P).eval₂ coefficients ξ/(j.factorial:L):=by
 let v:=polynomialPoint coefficients P γ ξ
 let h:=MvPolynomial.eval₂Hom coefficients v (polyH K F)
 have hH:h≠0:=hregular
 have hnum:MvPolynomial.eval₂Hom coefficients v (numerator K F j)=
     h^(2*j)*(Polynomial.derivative^[j] P).eval₂ coefficients ξ:=by
   rw [eval_polynomialPoint_eq_specialization,
     specialization_numerator_eq K F P γ hsolution j,
     Polynomial.eval₂_mul,Polynomial.eval₂_pow]
   rw [←eval_polynomialPoint_eq_specialization coefficients P γ ξ (polyH K F)]
 have hcancel:h^(2*j)*h⁻¹^(2*j)=1:=by
   rw [←mul_pow,mul_inv_cancel₀ hH,one_pow]
 rw [jetCoefficient_eq_evaluated_numerator,hnum]
 change (h^(2*j)*(Polynomial.derivative^[j] P).eval₂ coefficients ξ)*
     h⁻¹^(2*j)/(j.factorial:L)=_
 congr 1
 calc
   (h^(2*j)*(Polynomial.derivative^[j] P).eval₂ coefficients ξ)*h⁻¹^(2*j)=
       (h^(2*j)*h⁻¹^(2*j))*
         (Polynomial.derivative^[j] P).eval₂ coefficients ξ:=by ring
   _=(Polynomial.derivative^[j] P).eval₂ coefficients ξ:=by rw [hcancel,one_mul]
theorem polynomialPoint_jetCoefficient_eq_taylor_coeff
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (j:ℕ)
   (hfactorial:(j.factorial:L)≠0):
   jetCoefficient (contactDerivation K F)
       (regularPointValue coefficients F (polynomialPoint coefficients P γ ξ)
         (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular)
       (contactCoordinate K F (1:Fin 4)) j=
     (Polynomial.taylor ξ (P.map coefficients)).coeff j:=by
 rw [polynomialPoint_jetCoefficient_eq coefficients F P γ ξ hsolution hregular j,
   Polynomial.eval₂_eq_eval_map, ←Polynomial.iterate_derivative_map]
 exact (taylor_coeff_eq_derivative_div_factorial (P.map coefficients) ξ j hfactorial).symm
theorem reconstructedPolynomial_eq_taylor_of_solution
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p w:ℕ) [CharP L p] (hchar:w < p) (hdegree:P.natDegree ≤ w):
   reconstructedPolynomial coefficients F (polynomialPoint coefficients P γ ξ)
     (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w=
     Polynomial.taylor ξ (P.map coefficients):=by
 ext j
 simp only [reconstructedPolynomial,jetPolynomial_coeff]
 by_cases hj:j < w+1
 · rw [if_pos hj]
   exact polynomialPoint_jetCoefficient_eq_taylor_coeff coefficients F P γ ξ
     hsolution hregular j
     (factorial_cast_ne_zero_below_characteristic p j (by omega))
 · rw [if_neg hj]
   have hmap:(P.map coefficients).natDegree ≤ w:=
     Polynomial.natDegree_map_le.trans hdegree
   symm
   apply Polynomial.coeff_eq_zero_of_natDegree_lt
   rw [Polynomial.natDegree_taylor]
   omega
theorem globalPolynomial_eq_map_of_solution
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p w:ℕ) [CharP L p] (hchar:w < p) (hdegree:P.natDegree ≤ w):
   globalPolynomial coefficients F (polynomialPoint coefficients P γ ξ)
     (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w=
     P.map coefficients:=by
 change Polynomial.taylor (-ξ)
   (reconstructedPolynomial coefficients F (polynomialPoint coefficients P γ ξ)
     (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w)=_
 rw [reconstructedPolynomial_eq_taylor_of_solution coefficients F P γ ξ hsolution
   hregular p w hchar hdegree,Polynomial.taylor_taylor,neg_add_cancel,
   Polynomial.taylor_zero]
theorem factorial_agreement_zero_iff_original_agreement
   (coefficients:K →+*L) (F:Poly4 K) (P:Polynomial K) (γ:K) (ξ:L)
   (hsolution:specialization K P γ F=0)
   (hregular:MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p w:ℕ) [CharP L p] (hchar:w < p) (hdegree:P.natDegree ≤ w)
   (x u₀ u₁:K):
   MvPolynomial.eval₂Hom coefficients (polynomialPoint coefficients P γ ξ)
       (agreementNumerator F w (fun j:ℕ => (j.factorial:K)⁻¹) x u₀ u₁)=0 ↔
     P.eval x=u₀+γ*u₁:=by
 have heq:=factorial_agreement_zero_iff_actual_agreement coefficients F
   (polynomialPoint coefficients P γ ξ)
   (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w x u₀ u₁
 rw [←globalPolynomial_eval coefficients F (polynomialPoint coefficients P γ ξ)
     (polynomialPoint_relation coefficients F P γ ξ hsolution) hregular w (coefficients x),
   globalPolynomial_eq_map_of_solution coefficients F P γ ξ hsolution hregular
     p w hchar hdegree] at heq
 have hvalue:(P.map coefficients).eval (coefficients x)=coefficients (P.eval x):=by
   rw [←Polynomial.eval₂_eq_eval_map,Polynomial.eval₂_at_apply]
 have hseed:polynomialPoint coefficients P γ ξ (3:Fin 4)=coefficients γ:=rfl
 rw [hvalue,hseed, ←map_mul, ←map_add] at heq
 exact heq.trans coefficients.injective.eq_iff
end
end ProximityPrize.SubmissionLower.RCN229
end PackedLegacy_T

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.B0. -/
section PackedLegacy_B0
namespace ProximityPrize.SubmissionLower.RCN065
open RCN002 RCN136 RCN224 RCN139 RCN233 RCN231 RCN229 RCN313 RCN047 RCN147 RCN319
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
 (φ:Polynomial K →+*Ω)
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
def componentCoefficients:K →+*CoordinateField Ω P:=
 (algebraMap Ω (CoordinateField Ω P)).comp (φ.comp Polynomial.C)
def componentPoint:Fin 4 → CoordinateField Ω P:=
 Fin.cases (algebraMap Ω (CoordinateField Ω P) (φ Polynomial.X)) (coordinate Ω P)
theorem component_evaluation (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) F=
     coordinateEvaluation Ω P (surfaceMap φ F):=by
 have hhom:MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P)=
     (coordinateEvaluation Ω P).toRingHom.comp (surfaceMap φ):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [componentCoefficients,RingHom.comp_apply]
   · intro i
     refine Fin.cases ?_ (fun j => ?_) i
     · simp [componentPoint,RingHom.comp_apply]
     · simp only [MvPolynomial.eval₂Hom_X',RingHom.comp_apply,surfaceMap_X_succ]
       rfl
 exact RingHom.congr_fun hhom F
theorem component_evaluation_zero_iff (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) F=0 ↔
     surfaceMap φ F∈P:=by
 rw [component_evaluation]
 change surfaceMap φ F∈RingHom.ker (coordinateEvaluation Ω P).toRingHom ↔ _
 rw [coordinateEvaluation_ker]
variable (F:MvPolynomial (Fin 4) K)
 (hF:surfaceMap φ F∈P)
 (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
include hF in
theorem component_relation:
   MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) F=0:=
 (component_evaluation_zero_iff φ P F).mpr hF
include hH in
theorem component_regular:
   MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0:=
 (component_evaluation_zero_iff φ P _).not.mpr hH
def truncatedPolynomial (w:ℕ):Polynomial (CoordinateField Ω P):=
 globalPolynomial (componentCoefficients φ P) F (componentPoint φ P)
   (component_relation φ P F hF) (component_regular φ P F hH) w
theorem truncatedPolynomial_natDegree_le (w:ℕ):
   (truncatedPolynomial φ P F hF hH w).natDegree ≤ w:=
 globalPolynomial_natDegree_le _ _ _ _ _ _
theorem truncatedPolynomial_initial_value (w:ℕ):
   (truncatedPolynomial φ P F hF hH w).eval
     (algebraMap Ω (CoordinateField Ω P) (φ Polynomial.X))=coordinate Ω P 0:=
 globalPolynomial_initial_value (componentCoefficients φ P) F (componentPoint φ P)
   (component_relation φ P F hF) (component_regular φ P F hH) w
theorem truncatedPolynomial_initial_slope (w:ℕ) (hw:1 ≤ w):
   (truncatedPolynomial φ P F hF hH w).derivative.eval
     (algebraMap Ω (CoordinateField Ω P) (φ Polynomial.X))=coordinate Ω P 1:=
 globalPolynomial_initial_slope (componentCoefficients φ P) F (componentPoint φ P)
   (component_relation φ P F hF) (component_regular φ P F hH) w hw
theorem agreement_mem_iff_truncated_value (w:ℕ) (x u₀ u₁:K):
   surfaceMap φ (agreementNumerator F w (fun j => (j.factorial:K)⁻¹) x u₀ u₁)∈P ↔
     (truncatedPolynomial φ P F hF hH w).eval (componentCoefficients φ P x)=
       componentCoefficients φ P u₀+coordinate Ω P 2*componentCoefficients φ P u₁:=by
 rw [←component_evaluation_zero_iff]
 rw [factorial_agreement_zero_iff_actual_agreement (componentCoefficients φ P) F
   (componentPoint φ P) (component_relation φ P F hF) (component_regular φ P F hH)]
 rw [←globalPolynomial_eval]
 rfl
def identityNodes {ι:Type*} (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ):Finset ι:=by
 classical
 exact nodes.filter (fun i => surfaceMap φ
   (agreementNumerator F w (fun j => (j.factorial:K)⁻¹) (x i) (u₀ i) (u₁ i))∈P)
theorem identityNodes_subset {ι:Type*}
   (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ):
   identityNodes φ P F nodes x u₀ u₁ w ⊆ nodes:=by
 classical
 exact Finset.filter_subset _ _
theorem exists_common_pencil_of_many_identities {ι τ:Type*}
   (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ)
   (hinj:Set.InjOn x nodes)
   (hcard:w < (identityNodes φ P F nodes x u₀ u₁ w).card)
   (seed:τ → K) (selected:τ → Polynomial K)
   (hdegree:∀ t,(selected t).natDegree ≤ w)
   (hvalues:∀ t i,i∈identityNodes φ P F nodes x u₀ u₁ w →
     (selected t).eval (x i)=u₀ i+seed t*u₁ i):
   ∃ P₀ P₁:Polynomial K,P₀.natDegree ≤ w∧P₁.natDegree ≤ w∧
     truncatedPolynomial φ P F hF hH w=
       P₀.map (componentCoefficients φ P)+Polynomial.C (coordinate Ω P 2)*
         P₁.map (componentCoefficients φ P)∧
     ∀ t,selected t=P₀+Polynomial.C (seed t)*P₁:=by
 classical
 let I:=identityNodes φ P F nodes x u₀ u₁ w
 let seeds:Option τ → CoordinateField Ω P:=fun
   | none => coordinate Ω P 2
   | some t => componentCoefficients φ P (seed t)
 let polys:Option τ → Polynomial (CoordinateField Ω P):=fun
   | none => truncatedPolynomial φ P F hF hH w
   | some t => (selected t).map (componentCoefficients φ P)
 have hI:Set.InjOn x I:=hinj.mono (identityNodes_subset φ P F nodes x u₀ u₁ w)
 have hd:∀ t,(polys t).natDegree ≤ w:=by
   intro t
   cases t with
   | none => exact truncatedPolynomial_natDegree_le φ P F hF hH w
   | some t => exact Polynomial.natDegree_map_le.trans (hdegree t)
 have hv:∀ t i,i∈I → (polys t).eval (componentCoefficients φ P (x i))=
     componentCoefficients φ P (u₀ i)+seeds t*componentCoefficients φ P (u₁ i):=by
   intro t i hi
   cases t with
   | none =>
     apply (agreement_mem_iff_truncated_value φ P F hF hH w (x i) (u₀ i) (u₁ i)).mp
     exact (Finset.mem_filter.mp hi).2
   | some t =>
     change ((selected t).map (componentCoefficients φ P)).eval _=_
     rw [Polynomial.eval_map_apply,hvalues t i hi,map_add,map_mul]
 obtain ⟨P₀,P₁,h₀,h₁,hp⟩:=exists_basefield_affine_pencil_of_identity_nodes
   (componentCoefficients φ P) I x u₀ u₁ w hcard hI seeds polys hd hv
 refine ⟨P₀,P₁,h₀,h₁,hp none,?_⟩
 intro t
 apply Polynomial.map_injective (componentCoefficients φ P) (componentCoefficients φ P).injective
 simpa only [polys,seeds,Polynomial.map_add,Polynomial.map_mul,
   Polynomial.map_C] using hp (some t)
theorem coordinates_affine_of_basefield_pencil (w:ℕ) (hw:1 ≤ w)
   (P₀ P₁:Polynomial K)
   (hp:truncatedPolynomial φ P F hF hH w=
     P₀.map (componentCoefficients φ P)+Polynomial.C (coordinate Ω P 2)*
       P₁.map (componentCoefficients φ P)):
   coordinate Ω P 0=algebraMap Ω (CoordinateField Ω P)
       ((P₀.map (φ.comp Polynomial.C)).eval (φ Polynomial.X))+
     coordinate Ω P 2*algebraMap Ω (CoordinateField Ω P)
       ((P₁.map (φ.comp Polynomial.C)).eval (φ Polynomial.X))∧
   coordinate Ω P 1=algebraMap Ω (CoordinateField Ω P)
       ((P₀.map (φ.comp Polynomial.C)).derivative.eval (φ Polynomial.X))+
     coordinate Ω P 2*algebraMap Ω (CoordinateField Ω P)
       ((P₁.map (φ.comp Polynomial.C)).derivative.eval (φ Polynomial.X)):=by
 apply affine_coordinates_of_polynomial_pencil Ω P (φ Polynomial.X)
   (truncatedPolynomial φ P F hF hH w)
   (P₀.map (φ.comp Polynomial.C)) (P₁.map (φ.comp Polynomial.C))
 · simpa only [Polynomial.map_map,componentCoefficients] using hp
 · exact truncatedPolynomial_initial_value φ P F hF hH w
 · exact truncatedPolynomial_initial_slope φ P F hF hH w hw
include hF hH in
theorem seed_transcendental_of_many_identities {ι:Type*} [IsAlgClosed Ω]
   (nodes:Finset ι) (x u₀ u₁:ι → K) (w:ℕ) (hw:1 ≤ w)
   (hinj:Set.InjOn x nodes)
   (hcard:w < (identityNodes φ P F nodes x u₀ u₁ w).card)
   (hnonpoint:∀ v:Fin 3 → Ω,P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   Transcendental Ω (coordinate Ω P 2):=by
 obtain ⟨P₀,P₁,_,_,hp,_⟩:=
   exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hcard
     (fun t:Empty => t.elim) (fun t:Empty => t.elim)
     (fun t => t.elim) (fun t => t.elim)
 obtain ⟨hy,hr⟩:=coordinates_affine_of_basefield_pencil φ P F hF hH w hw P₀ P₁ hp
 exact seed_transcendental_of_affine_coordinates Ω P hnonpoint _ _ _ _ hy hr
theorem selected_agrees_on_identity_nodes {ι:Type*}
   (nodes:Finset ι) (x u₀ u₁:ι → K) (p w:ℕ) [CharP Ω p]
   (hw:w < p) (S:Polynomial K) (γ:K) (hdegree:S.natDegree ≤ w)
   (hsolution:specialization K S γ F=0)
   (hregular:MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:P ≤ RingHom.ker (MvPolynomial.aeval
     (fun i:Fin 3 => polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) i.succ)).toRingHom):
   ∀ i∈identityNodes φ P F nodes x u₀ u₁ w,
     S.eval (x i)=u₀ i+γ*u₁ i:=by
 classical
 intro i hi
 have hmem:=(Finset.mem_filter.mp hi).2
 have hz:=hpoint hmem
 change MvPolynomial.eval
   (fun i:Fin 3 => polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) i.succ)
   (surfaceMap φ (agreementNumerator F w (fun j => (j.factorial:K)⁻¹)
     (x i) (u₀ i) (u₁ i)))=0 at hz
 rw [eval_surfaceMap] at hz
 have hv:Fin.cases (φ Polynomial.X)
     (fun i:Fin 3 => polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X) i.succ)=
     polynomialPoint (φ.comp Polynomial.C) S γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv] at hz
 exact (factorial_agreement_zero_iff_original_agreement (φ.comp Polynomial.C) F S γ
   (φ Polynomial.X) hsolution hregular p w hw hdegree (x i) (u₀ i) (u₁ i)).mp hz
end
end ProximityPrize.SubmissionLower.RCN065
end PackedLegacy_B0

/- Library component HJ is loaded from Mathlib.Combinatorics.Enumerative.DoubleCounting. -/

/-! Packed from ProximityPrize.SubmissionLower.BX. -/
section PackedLegacy_BX
namespace ProximityPrize.SubmissionLower.RCN173
theorem enlarge_exempt_card_bound
   {q n a i w M:ℕ}
   (hiw:i ≤ w) (hwa:w ≤ a) (han:a ≤ n)
   (hcount:q*(a-i) ≤ (n-i)*M):
   q*(a-w) ≤ (n-w)*M:=by
 by_cases hqM:q ≤ M
 · calc
     q*(a-w) ≤ M*(a-w):=Nat.mul_le_mul_right _ hqM
     _ ≤ M*(n-w):=
       Nat.mul_le_mul_left _ (Nat.sub_le_sub_right han w)
     _=(n-w)*M:=Nat.mul_comm _ _
 · have hMq:M ≤ q:=(Nat.lt_of_not_ge hqM).le
   have ha:a-i=(a-w)+(w-i):=by omega
   have hn:n-i=(n-w)+(w-i):=by omega
   have hcount':
       q*(a-w)+q*(w-i) ≤
         (n-w)*M+(w-i)*M:=by
     simpa only [ha,hn,Nat.mul_add,Nat.add_mul] using hcount
   have hcancel:(w-i)*M ≤ q*(w-i):=by
     calc
       (w-i)*M ≤ (w-i)*q:=Nat.mul_le_mul_left _ hMq
       _=q*(w-i):=Nat.mul_comm _ _
   omega
section FiniteIncidence
variable {Seed Node:Type*} [DecidableEq Seed] [DecidableEq Node]
 (relation:Seed → Node → Prop)
 [∀ seed node,Decidable (relation seed node)]
theorem incidence_after_exempt_nodes
   (seeds:Finset Seed) (nodes identities:Finset Node) (a M:ℕ)
   (hidentities:identities ⊆ nodes)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed => relation seed node)).card ≤ M):
   seeds.card*(a-identities.card) ≤
     (nodes.card-identities.card)*M:=by
 have hremaining (seed:Seed) (hseed:seed∈seeds):
     a-identities.card ≤ ((nodes \ identities).filter (relation seed)).card:=by
   have hsub:(nodes.filter (relation seed)) \ identities ⊆
       (nodes \ identities).filter (relation seed):=by
     intro node hnode
     obtain ⟨hfiltered,hnot⟩:=Finset.mem_sdiff.mp hnode
     obtain ⟨hnodes,hagree⟩:=Finset.mem_filter.mp hfiltered
     exact Finset.mem_filter.mpr
       ⟨Finset.mem_sdiff.mpr ⟨hnodes,hnot⟩,hagree⟩
   calc
     a-identities.card ≤
         (nodes.filter (relation seed)).card-identities.card:=
       Nat.sub_le_sub_right (hagreement seed hseed) identities.card
     _ ≤ ((nodes.filter (relation seed)) \ identities).card:=
       Finset.le_card_sdiff identities (nodes.filter (relation seed))
     _ ≤ ((nodes \ identities).filter (relation seed)).card:=
       Finset.card_le_card hsub
 have hdouble:seeds.card • (a-identities.card) ≤
     (nodes \ identities).card • M:=
   Finset.card_nsmul_le_card_nsmul (R:=ℕ) (r:=relation)
     (s:=seeds) (t:=nodes \ identities) hremaining hfiber
 simpa [nsmul_eq_mul,Finset.card_sdiff_of_subset hidentities] using hdouble
end FiniteIncidence
end ProximityPrize.SubmissionLower.RCN173
end PackedLegacy_BX
end Compact_PackedLegacyCore1
